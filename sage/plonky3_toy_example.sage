p = 2^31 - 1
F = FiniteField(p)
assert(not F(6).is_square())
assert(not F(-1).is_square())
ab = Curve_EdwardsToWeierstrass(F, -1,6)
E = EllipticCurve([ab[0],ab[1]])

print(E)
print(E.abelian_group())
#Elliptic Curve defined by y^2 = x^3 + 1386916523*x + 265949941 over Finite Field of size 2147483647
#Additive abelian group isomorphic to Z/1073725088 + Z/2 embedded in Abelian group of points on Elliptic Curve defined by y^2 = x^3 + 1386916523*x + 265949941 over Finite Field of size 2147483647
print(E.order().factor())
2^6 * 33553909
# sage: h = E.random_point()
# sage: h
# (930622938 : 1647937444 : 1)

h = F(64) * E(930622938, 1647937444)
print(h.order())
#33553909
print(h)
(1507648288 : 1742713665 : 1)

he = Point_WeierstrassToEdwards(F, E.a4(), E.a6(), h[0],h[1], -1, 6)
print(he)
#(310816354, 2077510353)

AB = Curve_EdwardsToMontgomery(F, F(-1),F(6))
AB
UV = Curve_MontgomeryToWeierstrass(F, AB[0], AB[1])
UV
Curve_WeierstrassToMontgomery(F, UV[0], UV[1])
Curve_MontgomeryToEdwards(F, AB[0], AB[1])

#he = Point_WeierstrassToEdwards(F, E.a4(), E.a6(), h[0],h[1], -1, 6)
#Edwards:  2147483646 6
#(920350133, 1227133512)
#(1386916523, 265949941)
#(1124830562, 3396292)

# generate public keys and aggregate them
b = [1,0,1,1,0]
pks_ws = []
pks = []

apk_ws = E.abelian_group().identity()
for i in range(0,5):
    current_pubkey_ws = E.random_point()
    if b[i] == 1:
        apk_ws = apk_ws + current_pubkey_ws
        pks_ws.append(current_pubkey_ws)
    pks.append(Point_WeierstrassToEdwards(F, E.a4(), E.a6(), pks_ws[i][0],pks_ws[i][1], -1, 6))

apk = Point_WeierstrassToEdwards(F, E.a4(), E.a6(), apk_ws[0],apk_ws[1], -1, 6)

print(pks_ws)
print(apk_ws)

#[(1763544472 : 347099778 : 1), (632754479 : 974697260 : 1), (1588884550 : 1548681017 : 1), (10313972 : 1436747175 : 1), (1781776409 : 123310436 : 1), (2080773035 : 194022205 : 1), (1570040396 : 1471743857 : 1), (1232543574 : 1353759032 : 1)]
#(1079337493 : 1894660795 : 1)

print(pks)
print(apk)
# [(1452990225, 221038753), (1415979279, 1396649897), (2387338, 1532407746), (761104766, 8593518), (346876432, 1281517386), (1452990225, 221038753), (1415979279, 1396649897), (2387338, 1532407746), (761104766, 8593518), (346876432, 1281517386)]
#(445907341, 511523144)

for i in range(0,5):
    print(pks[i][0])

for i in range(0,5):
    print(pks[i][1])
