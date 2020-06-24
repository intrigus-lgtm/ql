/**
 * @name Failure to use HTTPS URLs
 * @description Non-HTTPS connections can be intercepted by third parties.
 * @kind path-problem
 * @problem.severity recommendation
 * @precision medium
 * @id java/non-https-url
 * @tags security
 *       external/cwe/cwe-319
 */

import java
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.frameworks.Networking
import DataFlow::PathGraph

class HTTPFTPString extends StringLiteral {
  HTTPFTPString() {
    // Avoid matching "https" here.
    exists(string s | this.getRepresentedString() = s |
      (
        // Either the literal `http` or `ftp`, ...
        s = ["http", "ftp"]
        or
        // ... or the beginning of a `http` or `ftp` URL.
        s.matches(["http://%", "ftp://%"])
      ) and
      not s.matches("%/localhost%")
    )
  }
}

class UnsafeExtensionString extends StringLiteral {
  UnsafeExtensionString() {
    exists(string s | this.getRepresentedString() = s |
      // Either the literal `http` or `ftp`, ...
      s.matches("%." + unsafeExtension())
    )
  }
}

string unsafeExtension() {
  result =
    ["exe", "dmg", "pkg", "tar.gz", "zip", "sh", "bat", "cmd", "app", "apk", "msi", "dmg", "tar.gz",
        "zip", "js", "py", "jar", "war"]
}

class URLConstructor extends ClassInstanceExpr {
  Constructor c;

  URLConstructor() { c = getConstructor() and c.getDeclaringType() instanceof TypeUrl }

  Expr protocolArg() {
    // In all cases except where the first parameter is a URL, the argument
    // containing the protocol is the first one, otherwise it is the second.
    if c.getParameter(0).getType() instanceof TypeUrl
    then result = this.getArgument(1)
    else result = this.getArgument(0)
  }

  Expr pathArg() {
    // If the last parameter is a `URLStreamHandler`, then the argument
    // containing the path is the one before the last one.
    // If the last parameter is not a `URLStreamHandler`, it is also the path.
    if c.getParameter(c.getNumberOfParameters()).getType() instanceof TypeURLStreamHandler
    then result = this.getArgument(c.getNumberOfParameters() - 1)
    else result = this.getArgument(c.getNumberOfParameters())
  }
}

class HTTPFTPStringToURLCreationFlowConfig extends TaintTracking::Configuration {
  HTTPFTPStringToURLCreationFlowConfig() { this = "HTTPFTPStringToURLCreationFlowConfig" }

  override predicate isSource(DataFlow::Node src) { src.asExpr() instanceof HTTPFTPString }

  override predicate isSink(DataFlow::Node sink) {
    exists(URLConstructor c | c.protocolArg() = sink.asExpr())
  }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    exists(URLConstructor u |
      node1.asExpr() = u.protocolArg() and
      node2.asExpr() = u
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    node.getType() instanceof PrimitiveType or node.getType() instanceof BoxedType
  }
}

class UnsafeExtensionStringFlowConfig extends TaintTracking::Configuration {
  UnsafeExtensionStringFlowConfig() { this = "UnsafeExtensionStringFlowConfig" }

  override predicate isSource(DataFlow::Node src) { src.asExpr() instanceof UnsafeExtensionString }

  override predicate isSink(DataFlow::Node sink) {
    exists(URLConstructor c | c.pathArg() = sink.asExpr())
  }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    exists(URLConstructor u |
      node1.asExpr() = u.protocolArg() and
      node2.asExpr() = u
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    node.getType() instanceof PrimitiveType or node.getType() instanceof BoxedType
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink, URLConstructor m, HTTPFTPString s
where
  source.getNode().asExpr() = s and
  sink.getNode().asExpr() = m.protocolArg() and
  any(HTTPFTPStringToURLCreationFlowConfig c).hasFlowPath(source, sink)
select m, source, sink, "URL may have been constructed with HTTP or FTP protocol, using $@.", s,
  "this source"
