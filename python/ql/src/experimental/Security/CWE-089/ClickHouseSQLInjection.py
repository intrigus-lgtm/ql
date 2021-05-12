from django.conf.urls import url
from clickhouse_driver import Client
from clickhouse_driver import connect
from aioch import Client as aiochClient

class MyClient(Client):
    def dummy(self):
        return None

def show_user(request, username):

    # BAD -- async library 'aioch'
    aclient = aiochClient("localhost")
    progress = await aclient.execute_with_progress("SELECT * FROM users WHERE username = '%s'" % username)

    # BAD -- client excute
    client = Client('localhost')
    client.execute("SELECT * FROM users WHERE username = '%s'" % username)

    # BAD -- client excute oneliner
    Client('localhost').execute("SELECT * FROM users WHERE username = '%s'" % username)

    # GOOD -- send username through params
    query = "SELECT * FROM users WHERE username = %(username)s"
    Client('localhost').execute(query, {"username": username})

    # BAD -- PEP249 interface
    conn = connect('clickhouse://localhost')
    cursor = conn.cursor()
    cursor.execute("SELECT * FROM users WHERE username = '%s'" % username)

    # BAD -- MyClient is a subclass of Client
    MyClient('localhost').execute("SELECT * FROM users WHERE username = '%s'" % username)

urlpatterns = [url(r'^users/(?P<username>[^/]+)$', show_user)]
