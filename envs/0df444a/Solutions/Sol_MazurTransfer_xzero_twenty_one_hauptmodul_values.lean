-- Prove2me | solution 1 for MazurTransfer.xzero_twenty_one_hauptmodul_values
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T11:26:08.702116+00:00
-- url     : https://prove2.me/submissions/f0c75fc7-7f67-47f7-96e9-80f52cad2589

import Mathlib
import Theorems.Thm_MazurTransfer_xzero_twenty_one_affine_classification


/- Source module: MazurTorsion.NumberTheory.XZeroTwentyOneDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The elementary two-descent boundary for `X₀(21)`

The conductor-`21` elliptic curve

`y² + xy = x³ - 4x - 1`

is a standard model of `X₀(21)`.  Completing the square and making the
integral change of coordinates

`V = 4x + 1`, `W = 8y + 4x`

gives the full rational two-torsion model

`W² = V(V - 9)(V + 7)`.

This file carries out the denominator and local parts of the complete
two-descent on this model.  Every nonzero rational abscissa has one of the
eight squareclasses `±1`, `±3`, `±7`, `±21`.  Two classes are impossible
modulo sixteen, and translation by `(0,0)`, expressed by

`(V,W) ↦ (-63/V, 63W/V²)`,

pairs the other four local branches with them.  The two remaining
homogeneous spaces are

`c² = m⁴ - 2m²n² - 63n⁴`

and

`c² = -3m⁴ - 2m²n² + 21n⁴`.

They are everywhere locally soluble and require genuine infinite descent.
Rather than conceal those global steps, the final rational-point
classification takes their precise primitive classifications as explicit
hypotheses.

The plane equation obtained by eliminating `j` between the classical
`X₀(3)` and `X₀(7)` hauptmoduls is also recorded, together with its four
visible noncuspidal points.  No modular interpretation or birational map
from that plane model is asserted here.
-/

namespace MazurTorsion.XZeroTwentyOne











/-- The affine equation of the full-two-torsion model. -/
def OnFullTwoCurve (V W : ℚ) : Prop :=
  W ^ 2 = V * (V - 9) * (V + 7)











/-- The denominator-free fibre-product equation for the classical
hauptmoduls on `X₀(3)` and `X₀(7)`. -/
def HauptmodulPair (t₃ t₇ : ℚ) : Prop :=
  (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 =
    t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3



















































end MazurTorsion.XZeroTwentyOne

end


/- Source module: MazurTorsion.NumberTheory.XZeroTwentyOneReduction. Original headers retained. -/
section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rational points on the split `X₀(21)` model

The two-isogeny descent proves that the rational point group of

`W² = V(V - 9)(V + 7)`

is finite and exhibits eight distinct points.  This file applies good
reduction at five.  The reduced curve has exactly eight points, and the
reduction map is injective on the finite rational point group.
Consequently the eight visible points exhaust the rational points, and
every finite point has abscissa `0`, `9`, `-7`, `-3`, or `21`.

This closes both quartic leaves isolated by `XZeroTwentyOneDescent`:
`PrincipalQuarticClassified` and `NegativeThreeQuarticClassified` become
theorems, and the conditional classifications of that file hold
unconditionally.
-/

open WeierstrassCurve

namespace MazurTorsion.XZeroTwentyOne

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum














































/-! ## The two quartic leaves become theorems -/









/-! ## The unconditional classifications -/



/-- Every affine rational solution of the split model is one of the seven
listed points, unconditionally. -/
theorem fullTwo_affine_classification_unconditional
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) :=
  MazurTransfer.xzero_twenty_one_affine_classification V W hcurve

end MazurTorsion.XZeroTwentyOne

end


/- Source module: MazurTorsion.NumberTheory.SevenAdicCertificates. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Seven-adic certificates for the level-seven CM loci

The quadratic `t² + 245t + 2401` and the quartic
`t⁴ - 490t³ - 21609t² - 235298t - 823543` cut out the complex
multiplication fibres (over `j = 0` and `j = 1728`) of the degeneracy
loci of level-seven hauptmodul correspondences.  Neither has a rational
root: the quadratic dies modulo eight and the quartic modulo five.
Both facts are shared by the `X₀(21)` and `X₀(49)` transfer files.
-/

namespace MazurTorsion

private abbrev toTwo : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

private lemma quad_mod_eight :
    ∀ m n : ZMod 8, (toTwo m ≠ 0 ∨ toTwo n ≠ 0) →
      m ^ 2 + 245 * m * n + 2401 * n ^ 2 ≠ 0 := by
  decide

private lemma intCast_toTwo_ne_zero
    {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    toTwo (m : ZMod 8) ≠ 0 := by
  intro h
  apply hm
  have h2 : ((m : ZMod 2) : ZMod 2) = 0 := by
    simpa [toTwo] using h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2

/-- The quadratic factor `t₇² + 245t₇ + 2401` has no rational root. -/
lemma levelSevenQuadratic_ne_zero (t₇ : ℚ) :
    t₇ ^ 2 + 245 * t₇ + 2401 ≠ 0 := by
  intro hq
  let m : ℤ := t₇.num
  let n : ℤ := (t₇.den : ℤ)
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast t₇.den_ne_zero
  have ht : t₇ = (m : ℚ) / n := t₇.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den t₇
  have hclearedQ :
      ((m ^ 2 + 245 * m * n + 2401 * n ^ 2 : ℤ) : ℚ) = 0 := by
    rw [ht] at hq
    field_simp at hq
    push_cast
    linear_combination hq
  have hcleared : m ^ 2 + 245 * m * n + 2401 * n ^ 2 = 0 := by
    exact_mod_cast hclearedQ
  have hodd : ¬ (2 : ℤ) ∣ m ∨ ¬ (2 : ℤ) ∣ n := by
    by_contra hcon
    push Not at hcon
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' hcon.1 hcon.2
    norm_num [Int.isUnit_iff] at this
  apply quad_mod_eight (m : ZMod 8) (n : ZMod 8)
    (hodd.imp intCast_toTwo_ne_zero intCast_toTwo_ne_zero)
  have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hcleared
  push_cast at this
  linear_combination this

private lemma quartic_mod_five :
    ∀ m n : ZMod 5, (m ≠ 0 ∨ n ≠ 0) →
      m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
        235298 * m * n ^ 3 - 823543 * n ^ 4 ≠ 0 := by
  decide

/-- The quartic factor has no rational root. -/
lemma levelSevenQuartic_ne_zero (t₇ : ℚ) :
    t₇ ^ 4 - 490 * t₇ ^ 3 - 21609 * t₇ ^ 2 -
      235298 * t₇ - 823543 ≠ 0 := by
  intro hq
  let m : ℤ := t₇.num
  let n : ℤ := (t₇.den : ℤ)
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast t₇.den_ne_zero
  have ht : t₇ = (m : ℚ) / n := t₇.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den t₇
  have hclearedQ :
      ((m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
        235298 * m * n ^ 3 - 823543 * n ^ 4 : ℤ) : ℚ) = 0 := by
    rw [ht] at hq
    field_simp at hq
    push_cast
    linear_combination hq
  have hcleared : m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
      235298 * m * n ^ 3 - 823543 * n ^ 4 = 0 := by
    exact_mod_cast hclearedQ
  have hnotboth : ((m : ZMod 5) ≠ 0 ∨ (n : ZMod 5) ≠ 0) := by
    by_contra hcon
    push Not at hcon
    have h5m : (5 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp hcon.1
    have h5n : (5 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp hcon.2
    have : IsUnit (5 : ℤ) := hmn.isUnit_of_dvd' h5m h5n
    norm_num [Int.isUnit_iff] at this
  apply quartic_mod_five (m : ZMod 5) (n : ZMod 5) hnotboth
  have := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hcleared
  push_cast at this
  linear_combination this


end MazurTorsion

end


/- Source module: MazurTorsion.NumberTheory.XZeroTwentyOneTransfer. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Transfer from the hauptmodul plane model to the split `X₀(21)` curve

The recorded fibre-product equation `HauptmodulPair t₃ t₇` is a plane
model of `X₀(21)`.  This file carries an explicit birational map from its
rational solutions to the split Weierstrass model `W² = V(V-9)(V+7)` and
transports the unconditional eight-point classification back: every
rational solution with `t₃ ≠ 0` and `t₇ ≠ 0` has

`t₃ ∈ {-18, -1152, -81/2, -81/128}`,

the four exceptional values already excluded on the order-seven Tate
family.  The map was discovered by exact q-expansion fits against the
level-21 newform; every identity used here is verified purely
algebraically.
-/

namespace MazurTorsion.XZeroTwentyOne

/-- Numerator of the transfer abscissa. -/
private def tVn (t₃ t₇ : ℚ) : ℚ :=
  -3*t₃^2*t₇^4 + 441*t₃^2*t₇^3 + 7203*t₃^2*t₇^2 - 75*t₃*t₇^4 + 18228*t₃*t₇^3 + 583443*t₃*t₇^2
  + 4941258*t₃*t₇ + 17294403*t₃ - 108*t₇^4 + 80703*t₇^3 + 3889620*t₇^2 + 44471322*t₇ + 155649627

/-- Denominator of the transfer abscissa. -/
private def tVd (t₃ t₇ : ℚ) : ℚ :=
  t₃^2*t₇^4 + 77*t₃^2*t₇^3 + 343*t₃^2*t₇^2 + 21*t₃*t₇^4 - 84*t₃*t₇^3 - 58653*t₃*t₇^2
  - 705894*t₃*t₇ - 2470629*t₃ - 15309*t₇^3 - 592704*t₇^2 - 6353046*t₇ - 22235661

/-- Cleared numerator of the transfer ordinate. -/
private def tBh (t₃ t₇ : ℚ) : ℚ :=
  1728*t₃^6*t₇^12 + 399168*t₃^6*t₇^11 + 606928896*t₃^6*t₇^10 + 22798359360*t₃^6*t₇^9
  + 307385777664*t₃^6*t₇^8 + 1743275822400*t₃^6*t₇^7 + 3416820611904*t₃^6*t₇^6
  + 108864*t₃^5*t₇^12 - 15023232*t₃^5*t₇^11 + 45793496448*t₃^5*t₇^10 + 2253291094656*t₃^5*t₇^9
  + 45574210785600*t₃^5*t₇^8 + 513359864180352*t₃^5*t₇^7 + 3526158871484928*t₃^5*t₇^6
  + 14063633638596864*t₃^5*t₇^5 + 24611358867544512*t₃^5*t₇^4 + 2856384*t₃^4*t₇^12
  - 1878920064*t₃^4*t₇^11 + 1232503667136*t₃^4*t₇^10 + 82150330248000*t₃^4*t₇^9
  + 2355582599177472*t₃^4*t₇^8 + 40129930507516416*t₃^4*t₇^7 + 445813086158786304*t₃^4*t₇^6
  + 3283858454612367744*t₃^4*t₇^5 + 15652824239758309632*t₃^4*t₇^4
  + 44620393626858200256*t₃^4*t₇^3 + 59091872640974373312*t₃^4*t₇^2 - 3456*t₃^3*t₇^13
  + 41565312*t₃^3*t₇^12 - 44016835968*t₃^3*t₇^11 + 13503719851776*t₃^3*t₇^10
  + 1290424314170880*t₃^3*t₇^9 + 48953055023139456*t₃^3*t₇^8 + 1051362256999953024*t₃^3*t₇^7
  + 14118330102952223232*t₃^3*t₇^6 + 122142658151213763840*t₃^3*t₇^5
  + 673547261914379841408*t₃^3*t₇^4 + 2231019681342910012800*t₃^3*t₇^3
  + 3781879849022359891968*t₃^3*t₇^2 + 1930334506271829528192*t₃^3*t₇ - 93312*t₃^2*t₇^13
  + 351459648*t₃^2*t₇^12 - 346571265600*t₃^2*t₇^11 + 49512122529408*t₃^2*t₇^10
  + 8186345863738560*t₃^2*t₇^9 + 405656549704514304*t₃^2*t₇^8 + 10386607423848433344*t₃^2*t₇^7
  + 158440148288718262848*t₃^2*t₇^6 + 1518112996751977081344*t₃^2*t₇^5
  + 9187026483512485617408*t₃^2*t₇^4 + 33733017581904799393536*t₃^2*t₇^3
  + 67010183574864939335808*t₃^2*t₇^2 + 52119031669339397261184*t₃^2*t₇ - 839808*t₃*t₇^13
  + 1777453632*t₃*t₇^12 - 813511931904*t₃*t₇^11 + 68428126069632*t₃*t₇^10
  + 19412291672855424*t₃*t₇^9 + 1226916153376861248*t₃*t₇^8 + 37163461077392073984*t₃*t₇^7
  + 645671342795038995456*t₃*t₇^6 + 6923779985686730890752*t₃*t₇^5
  + 46817818803346912009920*t₃*t₇^4 + 195169601723877767919744*t₃*t₇^3
  + 459498401656216726874112*t₃*t₇^2 + 469071285024054575350656*t₃*t₇ - 2519424*t₇^13
  + 2422426176*t₇^12 - 612091541376*t₇^11 - 19915919489088*t₇^10 + 5566854451919040*t₇^9
  + 556401147850050048*t₇^8 + 23497472558822492160*t₇^7 + 546769167246385292160*t₇^6
  + 7673913108519029721216*t₇^5 + 66982274293909143859200*t₇^4 + 357810936493775907852864*t₇^3
  + 1076949378881757953611200*t₇^2 + 1407213855072163726051968*t₇

/-- Cleared denominator core of the transfer ordinate,
`tVn² + 18·tVn·tVd + 189·tVd²`. -/
private def tCh (t₃ t₇ : ℚ) : ℚ :=
  144*t₃^4*t₇^8 + 30240*t₃^4*t₇^7 + 2123856*t₃^4*t₇^6 + 29042496*t₃^4*t₇^5 + 118590192*t₃^4*t₇^4
  + 5904*t₃^3*t₇^8 + 799344*t₃^3*t₇^7 + 30129120*t₃^3*t₇^6 - 665557200*t₃^3*t₇^5
  - 18737250336*t₃^3*t₇^4 - 133651146384*t₃^3*t₇^3 - 284735050992*t₃^3*t₇^2 + 59328*t₃^2*t₇^8
  - 634032*t₃^2*t₇^7 - 479003616*t₃^2*t₇^6 - 17486002800*t₃^2*t₇^5 + 112304911824*t₃^2*t₇^4
  + 7455409600464*t₃^2*t₇^3 + 83996840042640*t₃^2*t₇^2 + 390656489961024*t₃^2*t₇
  + 683648857431792*t₃^2 - 24624*t₃*t₇^8 - 86229360*t₃*t₇^7 - 4746669984*t₃*t₇^6
  + 116467669584*t₃*t₇^5 + 9405150947136*t₃*t₇^4 + 181108925189136*t₃*t₇^3
  + 1611885123665712*t₃*t₇^2 + 7031816819298432*t₃*t₇ + 12305679433772256*t₃ + 11664*t₇^8
  + 12328848*t₇^7 + 28881428688*t₇^6 + 2127587911344*t₇^5 + 62495370921312*t₇^4
  + 928660463350704*t₇^3 + 7495650217364400*t₇^2 + 31643175686842944*t₇ + 55375557451975152

private lemma hauptmodulPair_sub {t₃ t₇ : ℚ} (h : HauptmodulPair t₃ t₇) :
    (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 -
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 = 0 := by
  unfold HauptmodulPair at h
  linear_combination h

/-- The transfer denominator does not vanish at a noncuspidal rational
solution of the fibre-product equation. -/
private lemma tVd_ne_zero {t₃ t₇ : ℚ} (h7 : t₇ ≠ 0)
    (hF : (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 -
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 = 0) :
    tVd t₃ t₇ ≠ 0 := by
  intro h0
  have hR :
      (-27 : ℚ) * t₇ ^ 6 * (t₇ ^ 2 + 245 * t₇ + 2401) ^ 4 *
        (t₇ ^ 4 - 490 * t₇ ^ 3 - 21609 * t₇ ^ 2 -
          235298 * t₇ - 823543) ^ 4 = 0 := by
    have hVd0 : tVd t₃ t₇ = 0 := h0
    unfold tVd at hVd0
    linear_combination
      (-t₃^3*t₇^27 + 722*t₃^3*t₇^26 + 50372*t₃^3*t₇^25 - 66059056*t₃^3*t₇^24 - 7107058441*t₃^3*t₇^23
      - 312300682288*t₃^3*t₇^22 - 7478532217275*t₃^3*t₇^21 - 110148398595060*t₃^3*t₇^20
      - 1135553043257241*t₃^3*t₇^19 - 10591131505609984*t₃^3*t₇^18 - 107508530392659235*t₃^3*t₇^17
      - 952854585291599872*t₃^3*t₇^16 - 5653852011945078928*t₃^3*t₇^15
      - 18990559378831656238*t₃^3*t₇^14 - 27368747340080916343*t₃^3*t₇^13 - 36*t₃^2*t₇^27
      + 25263*t₃^2*t₇^26 + 2333898*t₃^2*t₇^25 - 2337201657*t₃^2*t₇^24 - 303711599394*t₃^2*t₇^23
      - 16808988637854*t₃^2*t₇^22 - 538864923359826*t₃^2*t₇^21 - 11269551463707537*t₃^2*t₇^20
      - 164028637724572278*t₃^2*t₇^19 - 1731719179920662982*t₃^2*t₇^18
      - 13563336963125216358*t₃^2*t₇^17 - 78452081906531701473*t₃^2*t₇^16
      - 319875796691941138866*t₃^2*t₇^15 - 819386782610177638269*t₃^2*t₇^14
      - 985274904242912988348*t₃^2*t₇^13 - 270*t₃*t₇^27 + 168696*t₃*t₇^26 + 31807188*t₃*t₇^25
      - 15987468042*t₃*t₇^24 - 3608901781191*t₃*t₇^23 - 319347051257052*t₃*t₇^22
      - 16063779441281607*t₃*t₇^21 - 522437927264509662*t₃*t₇^20 - 11712446127453853908*t₃*t₇^19
      - 187402386367907142012*t₃*t₇^18 - 2176384900156015796919*t₃*t₇^17
      - 18403211530811616132330*t₃*t₇^16 - 112160683054949431594230*t₃*t₇^15
      - 479688124808549637755712*t₃*t₇^14 - 1364852061102495217109067*t₃*t₇^13
      - 2317366574779331348594496*t₃*t₇^12 - 1774233783815425563767661*t₃*t₇^11 + t₇^28 - 730*t₇^27
      - 44544*t₇^26 + 66423791*t₇^25 + 6576483403*t₇^24 + 258964978734*t₇^23 + 5269532945859*t₇^22
      + 52622752261086*t₇^21 + 3661321583279934*t₇^20 + 1073587261412828120*t₇^19
      + 122059778613488543191*t₇^18 + 7642670479849219158183*t₇^17 + 305275283347479111767275*t₇^16
      + 8371634189260220187178436*t₇^15 + 164357255777180700772910358*t₇^14
      + 2366365281042235654418030388*t₇^13 + 25275312047619358432490344401*t₇^12
      + 200403254349519948278684845272*t₇^11 + 1166472038252684806461733050283*t₇^10
      + 4852381874481682782445639560965*t₇^9 + 13683858883882176807722657100390*t₇^8
      + 23486758920471216464328492808466*t₇^7 + 18562115921017574302453163671207*t₇^6) * hVd0 +
      (t₃*t₇^24 - 645*t₃*t₇^23 - 105623*t₃*t₇^22 + 61932766*t₃*t₇^21 + 12176328157*t₃*t₇^20
      + 882202438453*t₃*t₇^19 + 33963405798714*t₃*t₇^18 + 793114513350019*t₃*t₇^17
      + 12182116285602186*t₃*t₇^16 + 135809616554523121*t₃*t₇^15 + 1312520350161861666*t₃*t₇^14
      + 12863769531950585479*t₃*t₇^13 + 115899081004080386677*t₃*t₇^12
      + 781166287053621489790*t₃*t₇^11 + 3428913059607280518973*t₃*t₇^10
      + 8621155412125488648045*t₃*t₇^9 + 9387480337647754305649*t₃*t₇^8 + 21*t₇^24 - 14517*t₇^23
      - 1520190*t₇^22 + 1352359722*t₇^21 + 191688706629*t₇^20 + 11361254869377*t₇^19
      + 382106898071556*t₇^18 + 8163021599986995*t₇^17 + 116004298635345834*t₇^16
      + 954097380628090461*t₇^15 - 5548536854970013359*t₇^14 - 430225310620203854553*t₇^13
      - 9708209423065000519791*t₇^12 - 133783384118825971028646*t₇^11
      - 1220509287630908464316085*t₇^10 - 7414768398122061936561903*t₇^9
      - 28979151802318617541538463*t₇^8 - 66238061262442554380659344*t₇^7
      - 67618020872076774263589747*t₇^6) * hF
  have h1 : (-27 : ℚ) * t₇ ^ 6 ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · exact h7 (pow_eq_zero_iff (by norm_num) |>.mp h)
  have h2 := pow_ne_zero 4 (MazurTorsion.levelSevenQuadratic_ne_zero t₇)
  have h3 := pow_ne_zero 4 (MazurTorsion.levelSevenQuartic_ne_zero t₇)
  exact mul_ne_zero (mul_ne_zero h1 h2) h3 hR

/-- The ordinate denominator core is positive once `tVd ≠ 0`. -/
private lemma tCh_ne_zero {t₃ t₇ : ℚ} (hVd : tVd t₃ t₇ ≠ 0) :
    tCh t₃ t₇ ≠ 0 := by
  have hsq : tCh t₃ t₇ =
      (tVn t₃ t₇ + 9 * tVd t₃ t₇) ^ 2 + 108 * tVd t₃ t₇ ^ 2 := by
    unfold tCh tVn tVd
    ring
  have hpos : 0 < tCh t₃ t₇ := by
    rw [hsq]
    have h108 : 0 < 108 * tVd t₃ t₇ ^ 2 := by positivity
    nlinarith [sq_nonneg (tVn t₃ t₇ + 9 * tVd t₃ t₇)]
  exact hpos.ne'

/-- Unfolded form of the ordinate numerator. -/
private lemma tBh_eq (t₃ t₇ : ℚ) :
    tBh t₃ t₇ =
      2 * (tVn t₃ t₇ + 3 * tVd t₃ t₇) ^ 3 * t₇ +
        9 * (tVn t₃ t₇ + 7 * tVd t₃ t₇) *
          (tVn t₃ t₇ ^ 2 - 6 * tVn t₃ t₇ * tVd t₃ t₇ +
            21 * tVd t₃ t₇ ^ 2) := by
  unfold tBh tVn tVd
  ring

/-- Unfolded form of the ordinate denominator core. -/
private lemma tCh_eq (t₃ t₇ : ℚ) :
    tCh t₃ t₇ =
      tVn t₃ t₇ ^ 2 + 18 * tVn t₃ t₇ * tVd t₃ t₇ +
        189 * tVd t₃ t₇ ^ 2 := by
  unfold tCh tVn tVd
  ring

/-- The transferred point satisfies the split Weierstrass equation. -/
private lemma transfer_on_curve {t₃ t₇ : ℚ}
    (hVd : tVd t₃ t₇ ≠ 0)
    (hF : (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 -
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 = 0) :
    OnFullTwoCurve (tVn t₃ t₇ / tVd t₃ t₇)
      (-(tBh t₃ t₇) / (tVd t₃ t₇ * tCh t₃ t₇)) := by
  have hCh := tCh_ne_zero hVd
  have key : tVd t₃ t₇ * tBh t₃ t₇ ^ 2 - tCh t₃ t₇ ^ 2 *
      (tVn t₃ t₇ ^ 3 - 2 * tVn t₃ t₇ ^ 2 * tVd t₃ t₇ -
        63 * tVn t₃ t₇ * tVd t₃ t₇ ^ 2) = 0 := by
    unfold tVn tVd tBh tCh
    linear_combination
      (2097546264576*t₃^10*t₇^19 + 739909444829184*t₃^10*t₇^18 + 438272197541756928*t₃^10*t₇^17
      + 58911128569895583744*t₃^10*t₇^16 + 3242937148286059413504*t₃^10*t₇^15
      + 96977711037688506482688*t₃^10*t₇^14 + 1773848586035742849368064*t₃^10*t₇^13
      + 20872272067975812863361024*t₃^10*t₇^12 + 159509504110537202457378816*t₃^10*t₇^11
      + 768962065942018392114069504*t₃^10*t₇^10 + 2134795537176141711818096640*t₃^10*t₇^9
      + 2615124533040773596977168384*t₃^10*t₇^8 - 112368549888*t₃^9*t₇^20
      + 230748817195008*t₃^9*t₇^19 + 41015862108684288*t₃^9*t₇^18 + 52759075389262921728*t₃^9*t₇^17
      + 7770348868693581692928*t₃^9*t₇^16 + 462648441143233097367552*t₃^9*t₇^15
      + 15242266292231763409895424*t₃^9*t₇^14 + 316574731078980592349085696*t₃^9*t₇^13
      + 4425659971923089636707074048*t₃^9*t₇^12 + 43082036662684503933113204736*t₃^9*t₇^11
      + 296068911471417894437947834368*t₃^9*t₇^10 + 1429298982027856279605011152896*t₃^9*t₇^9
      + 4695456099074708993372505833472*t₃^9*t₇^8 + 9610582658924842968891093811200*t₃^9*t₇^7
      + 9418371005746346109513271934976*t₃^9*t₇^6 + 2006581248*t₃^8*t₇^21
      - 11758064467968*t₃^8*t₇^20 + 12467037780836352*t₃^8*t₇^19 - 1214243362395979776*t₃^8*t₇^18
      + 2615762517710876835840*t₃^8*t₇^17 + 431290265795941358370816*t₃^8*t₇^16
      + 27753685724753029236916224*t₃^8*t₇^15 + 997308144130614269453402112*t₃^8*t₇^14
      + 22997960971429082970814414848*t₃^8*t₇^13 + 365664667566950842964687880192*t₃^8*t₇^12
      + 4178637603688121648444509913088*t₃^8*t₇^11 + 35160667387700984395735503863808*t₃^8*t₇^10
      + 220434984427176187896627000115200*t₃^8*t₇^9 + 1030128935059157209132470352478208*t₃^8*t₇^8
      + 3541691921466983130895745891303424*t₃^8*t₇^7 + 8655482954280892074642696908242944*t₃^8*t₇^6
      + 13845005378447128780984509744414720*t₃^8*t₇^5
      + 11306754392398488504470682957938688*t₃^8*t₇^4 - 11943936*t₃^7*t₇^22
      + 182336126976*t₃^7*t₇^21 - 546174443372544*t₃^7*t₇^20 + 461347735914971136*t₃^7*t₇^19
      - 157568175172217585664*t₃^7*t₇^18 + 68389999420252347629568*t₃^7*t₇^17
      + 13121095530103620629004288*t₃^7*t₇^16 + 915637388815944990765416448*t₃^7*t₇^15
      + 35687011691763318773342453760*t₃^7*t₇^14 + 900913592741289051807585239040*t₃^7*t₇^13
      + 15881241389335794424911733899264*t₃^7*t₇^12 + 204309727988297275387222223192064*t₃^7*t₇^11
      + 1971240063149127360810210169503744*t₃^7*t₇^10
      + 14496950934449625489479666447745024*t₃^7*t₇^9
      + 81892089305423685090946046869733376*t₃^7*t₇^8
      + 355346360381314487355357496240963584*t₃^7*t₇^7
      + 1175060297468678985350325382560104448*t₃^7*t₇^6
      + 2910143213853039541269716256555171840*t₃^7*t₇^5
      + 5236911742745899925654004656685268992*t₃^7*t₇^4
      + 6463694594321135928389073757621616640*t₃^7*t₇^3
      + 4524586216024795149872351630335131648*t₃^7*t₇^2 - 895795200*t₃^6*t₇^22
      + 7070690672640*t₃^6*t₇^21 - 15080556932775936*t₃^6*t₇^20 + 12347741460530036736*t₃^6*t₇^19
      - 5357105599816830763008*t₃^6*t₇^18 + 994558442803923655655424*t₃^6*t₇^17
      + 239086434651971552960348160*t₃^6*t₇^16 + 18260007641539565220666998784*t₃^6*t₇^15
      + 771064401167001337595310784512*t₃^6*t₇^14 + 21142156857082077512089716424704*t₃^6*t₇^13
      + 406988827360204675025974284140544*t₃^6*t₇^12 + 5755116918087277565159091632504832*t₃^6*t₇^11
      + 61477791119252577997011345362927616*t₃^6*t₇^10
      + 504553128307724612848897555811205120*t₃^6*t₇^9
      + 3208270316023043939624579693965246464*t₃^6*t₇^8
      + 15815932329651898045729991971724918784*t₃^6*t₇^7
      + 59966407940896015881532313527340679168*t₃^6*t₇^6
      + 171409242838312881800377138266538475520*t₃^6*t₇^5
      + 354506323842066009324921558121730654208*t₃^6*t₇^4
      + 484777094574085194629180531821621248000*t₃^6*t₇^3
      + 339343966201859636240426372275134873600*t₃^6*t₇^2 - 28056305664*t₃^5*t₇^22
      + 154323225575424*t₃^5*t₇^21 - 273585549199785984*t₃^5*t₇^20
      + 222751378437484216320*t₃^5*t₇^19 - 89956889213643190222848*t₃^5*t₇^18
      + 7568384457564753693179904*t₃^5*t₇^17 + 2683265070647228518541131776*t₃^5*t₇^16
      + 228256796916248309783687135232*t₃^5*t₇^15 + 10485098567461088020023646076928*t₃^5*t₇^14
      + 311506379355988176999918364753920*t₃^5*t₇^13 + 6497736782839595009402188763086848*t₃^5*t₇^12
      + 99675104446903653869821709692796928*t₃^5*t₇^11
      + 1156607794745529459012286973283778560*t₃^5*t₇^10
      + 10323023655255539198261990765823590400*t₃^5*t₇^9
      + 71425424268309415608265156680786739200*t₃^5*t₇^8
      + 382937693071206110783166457653392769024*t₃^5*t₇^7
      + 1575001390877712202553337667851476877312*t₃^5*t₇^6
      + 4853210879104133463975333815169955430400*t₃^5*t₇^5
      + 10682288000683516183613019373513213231104*t₃^5*t₇^4
      + 15183218602060348295785934256653177487360*t₃^5*t₇^3
      + 10628253021442243807050153979657224241152*t₃^5*t₇^2 - 478892113920*t₃^4*t₇^22
      + 2084399693660160*t₃^4*t₇^21 - 3284759538424627200*t₃^4*t₇^20
      + 2481606384765330751488*t₃^4*t₇^19 - 803947545308973425246208*t₃^4*t₇^18
      + 20474889175995078588825600*t₃^4*t₇^17 + 18430925380530906394150207488*t₃^4*t₇^16
      + 1797862098344693630000350298112*t₃^4*t₇^15 + 90734849418294816782601583411200*t₃^4*t₇^14
      + 2928893389513467864828735521193984*t₃^4*t₇^13
      + 66071735916445872062040396968902656*t₃^4*t₇^12
      + 1093041285498114797062439571081166848*t₃^4*t₇^11
      + 13646264331794671377015794144986742784*t₃^4*t₇^10
      + 130717414737834265776851489399126556672*t₃^4*t₇^9
      + 967724740245260378333016153843906281472*t₃^4*t₇^8
      + 5528757525291704539057903723470377779200*t₃^4*t₇^7
      + 24093729364441388946422092996721595236352*t₃^4*t₇^6
      + 78025967992436745551685853184491607654400*t₃^4*t₇^5
      + 178404726589012809720419856943423987630080*t₃^4*t₇^4
      + 259161834759305945048759912311838719180800*t₃^4*t₇^3
      + 181413284331514161534131938618287103426560*t₃^4*t₇^2 - 4832456785920*t₃^3*t₇^22
      + 17711189212889088*t₃^3*t₇^21 - 24700050038685450240*t₃^3*t₇^20
      + 15709782249425007378432*t₃^3*t₇^19 - 3723749961745588833042432*t₃^3*t₇^18
      - 78623059464573359520153600*t₃^3*t₇^17 + 74649920152290414387490750464*t₃^3*t₇^16
      + 8734496238417517445745671602176*t₃^3*t₇^15 + 492306546047848398307029773205504*t₃^3*t₇^14
      + 17399657009907001317104886008807424*t₃^3*t₇^13
      + 425688622611874265643161822628691968*t₃^3*t₇^12
      + 7589222569433470582074439462052855808*t₃^3*t₇^11
      + 101573998431812466970954093149064937472*t₃^3*t₇^10
      + 1037864825518572311292149170546656608256*t₃^3*t₇^9
      + 8153012319881806623250155385136098344960*t₃^3*t₇^8
      + 49134513490802651633138832045699442999296*t₃^3*t₇^7
      + 224299407289681698047769278280836352098304*t₃^3*t₇^6
      + 754491947787981588044445549396402973409280*t₃^3*t₇^5
      + 1773429392469218075209595519541538039775232*t₃^3*t₇^4
      + 2615178514389359990946577296964917984460800*t₃^3*t₇^3
      + 1830624960072551993662604107875442589122560*t₃^3*t₇^2 - 28916376551424*t₃^2*t₇^22
      + 90581607463550976*t₃^2*t₇^21 - 105726224675557785600*t₃^2*t₇^20
      + 52167729050529547714560*t₃^2*t₇^19 - 8836998227290356327235584*t₃^2*t₇^18
      - 669771533230141930933911552*t₃^2*t₇^17 + 163775851583874814338077786112*t₃^2*t₇^16
      + 24755837874904812574795011784704*t₃^2*t₇^15 + 1595766750103211912713432611864576*t₃^2*t₇^14
      + 62534979685060018732782796101746688*t₃^2*t₇^13
      + 1670998327978358678358980478750474240*t₃^2*t₇^12
      + 32212178707642674451189114783893258240*t₃^2*t₇^11
      + 462429005743388063206307170937446907904*t₃^2*t₇^10
      + 5031394561830944113502037302904861818880*t₃^2*t₇^9
      + 41789847403477109024005317374403555065856*t₃^2*t₇^8
      + 264339509124832535995294588525929686040576*t₃^2*t₇^7
      + 1256631594795987552096298221228492568412160*t₃^2*t₇^6
      + 4363972301925621022536052328421121072988160*t₃^2*t₇^5
      + 10488710129810606652650071065691651589357568*t₃^2*t₇^4
      + 15648662786102818972853303068865752479989760*t₃^2*t₇^3
      + 10954063950271973280997312148206026735992832*t₃^2*t₇^2 - 95212459376640*t₃*t₇^22
      + 245762400142983168*t₃*t₇^21 - 221852932981699461120*t₃*t₇^20
      + 84976677179545131122688*t₃*t₇^19 - 9555565636375870492459008*t₃*t₇^18
      - 1567307817878608724169129984*t₃*t₇^17 + 160608086129358775712500383744*t₃*t₇^16
      + 36363797611055832772101151457280*t₃*t₇^15 + 2769571985116461324149364163559424*t₃*t₇^14
      + 122477146395305193238087215842623488*t₃*t₇^13
      + 3614635607639829068055069514824302592*t₃*t₇^12
      + 75875611566326174944647800900777312256*t₃*t₇^11
      + 1172911574554569565829422597835299307520*t₃*t₇^10
      + 13608567707593933459291027408442519519232*t₃*t₇^9
      + 119442399211120492423823923859442343575552*t₃*t₇^8
      + 791375946291602307436692353481365590573056*t₃*t₇^7
      + 3905961315387513846749870695609009116856320*t₃*t₇^6
      + 13957140095519983171260831969588688133652480*t₃*t₇^5
      + 34199499888669746753436016628658673348165632*t₃*t₇^4
      + 51526084783509281983785266202362843531673600*t₃*t₇^3
      + 36068259348456497388649686341653990472171520*t₃*t₇^2 - 133297443127296*t₇^22
      + 251170467835576320*t₇^21 - 178131371635946373120*t₇^20 + 52995836789504550273024*t₇^19
      - 3002434806301717037432832*t₇^18 - 1198687168442983049952952320*t₇^17
      + 37066166368302612026770292736*t₇^16 + 20563438813499713137470963122176*t₇^15
      + 1934566115791522972447398593544192*t₇^14 + 98690092793766702399558623332368384*t₇^13
      + 3266146887734971878363719331800039424*t₇^12 + 75468696902357175030628133141094825984*t₇^11
      + 1265324795296824716070550140198591774720*t₇^10
      + 15720414105830059955667228100656873799680*t₇^9
      + 146055055419029910917215058370096620077056*t₇^8
      + 1013494172416968019026522471207848648441856*t₇^7
      + 5186787227481860585105269747457360574038016*t₇^6
      + 19035250813399722248903594802788772266803200*t₇^5
      + 47467091165869571198940141150503239939178496*t₇^4
      + 72136518696912994777299372683307980944343040*t₇^3
      + 50495563087839096344109560878315586661040128*t₇^2) * hF
  unfold OnFullTwoCurve
  field_simp
  linear_combination key

/-- Cleared ordinate relation used by the per-case analysis. -/
private lemma transfer_W_cleared {t₃ t₇ w : ℚ}
    (hVd : tVd t₃ t₇ ≠ 0)
    (hW : -(tBh t₃ t₇) / (tVd t₃ t₇ * tCh t₃ t₇) = w) :
    tBh t₃ t₇ = -(w * (tVd t₃ t₇ * tCh t₃ t₇)) := by
  have hCh := tCh_ne_zero hVd
  field_simp at hW
  linarith [hW]

/-- Cleared abscissa relation used by the per-case analysis. -/
private lemma transfer_V_cleared {t₃ t₇ v : ℚ}
    (hVd : tVd t₃ t₇ ≠ 0)
    (hV : tVn t₃ t₇ / tVd t₃ t₇ = v) :
    tVn t₃ t₇ = v * tVd t₃ t₇ := by
  field_simp at hV
  linear_combination hV

/-- The seven-adic resultant certificate for the `(-3,-12)` branch. -/
private lemma resultant_S {t₃ t₇ : ℚ}
    (hS : tVn t₃ t₇ + 3 * tVd t₃ t₇ = 0)
    (hF : (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 -
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 = 0) :
    (186624 : ℚ) * t₇ ^ 6 * (t₇ + 8) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 4 *
      (t₇ ^ 4 - 490 * t₇ ^ 3 - 21609 * t₇ ^ 2 -
        235298 * t₇ - 823543) ^ 4 = 0 := by
  have hS' : tVn t₃ t₇ + 3 * tVd t₃ t₇ = 0 := hS
  unfold tVn tVd at hS'
  linear_combination
    (1728*t₃^3*t₇^26 - 2540160*t₃^3*t₇^25 + 829192896*t₃^3*t₇^24 + 191506218624*t₃^3*t₇^23
      - 72238503915648*t₃^3*t₇^22 - 9768062550137472*t₃^3*t₇^21 - 512272687646470464*t₃^3*t₇^20
      - 14828953620174793344*t₃^3*t₇^19 - 265809707586300028032*t₃^3*t₇^18
      - 3087363709352832126336*t₃^3*t₇^17 - 23389527956565264701760*t₃^3*t₇^16
      - 112077585109048061381760*t₃^3*t₇^15 - 309818688256628639274816*t₃^3*t₇^14
      - 378345563229278587525632*t₃^3*t₇^13 + 46656*t₃^2*t₇^26 - 79035264*t₃^2*t₇^25
      + 29770929216*t₃^2*t₇^24 + 5814714294144*t₃^2*t₇^23 - 2632631108284800*t₃^2*t₇^22
      - 348775042087124352*t₃^2*t₇^21 - 18251232847064925120*t₃^2*t₇^20
      - 529010611132640337792*t₃^2*t₇^19 - 9502255799704815025536*t₃^2*t₇^18
      - 110592962311867462965888*t₃^2*t₇^17 - 839298750511942159685568*t₃^2*t₇^16
      - 4027347487972967438706048*t₃^2*t₇^15 - 11144786271960407781016512*t₃^2*t₇^14
      - 13620440276254029150922752*t₃^2*t₇^13 + 46656*t₃*t₇^26 - 305472384*t₃*t₇^25
      + 193001610816*t₃*t₇^24 + 17458780300416*t₃*t₇^23 - 17615536068961152*t₃*t₇^22
      - 1977881599100856960*t₃*t₇^21 - 87342461760161861568*t₃*t₇^20
      - 1912202272988684304768*t₃*t₇^19 - 17885672193474237237120*t₃*t₇^18
      + 97123854721708642794624*t₃*t₇^17 + 4773261784406817933661248*t₃*t₇^16
      + 61395864755245964127434880*t₃*t₇^15 + 434090728268649616555524672*t₃*t₇^14
      + 1809816001707254123428860672*t₃*t₇^13 + 4171259834602796427470092800*t₃*t₇^12
      + 4087834637910740498920690944*t₃*t₇^11 - 1728*t₇^27 + 1263168*t₇^26 + 381834432*t₇^25
      - 94312838592*t₇^24 - 172821757864896*t₇^23 - 11566297811117952*t₇^22
      + 15847517945621569536*t₇^21 + 3599307005241853209024*t₇^20 + 357513203103197810010048*t₇^19
      + 21014700823844776432742400*t₇^18 + 821959741015387025158513728*t₇^17
      + 22769279520644679783293397312*t₇^16 + 463588727115045738844491747264*t₇^15
      + 7094481933943218334485894925248*t₇^14 + 82594250424907694278246695768192*t₇^13
      + 734040721515830689739913795908352*t₇^12 + 4954574923209052045476998692077504*t₇^11
      + 25010823723136293013648376202937728*t₇^10 + 91627732517160407385007031230396224*t₇^9
      + 230498897425630124232029345680397184*t₇^8 + 356756291628112464797516151408079680*t₇^7
      + 256602690492146947157112534590765568*t₇^6) * hS' +
    (-1161216*t₃*t₇^22 + 1692762624*t₃*t₇^21 - 536307028992*t₃*t₇^20 - 135518094835200*t₃*t₇^19
      + 46967795439602688*t₃*t₇^18 + 7158805397925995520*t₃*t₇^17 + 424657937011159821312*t₃*t₇^16
      + 14182085597463205986816*t₃*t₇^15 + 300696069699272517645312*t₃*t₇^14
      + 4262853925535525019657216*t₃*t₇^13 + 41132940842204371943580672*t₃*t₇^12
      + 267858731331725556273431040*t₃*t₇^11 + 1130820839126138086887324672*t₃*t₇^10
      + 2804675660218642169327510016*t₃*t₇^9 + 3114540676503421332511002624*t₃*t₇^8 + 20736*t₇^23
      - 51093504*t₇^22 + 46696269312*t₇^21 - 11625694553088*t₇^20 - 3914016294085632*t₇^19
      + 1131411430679878656*t₇^18 + 196662181044870374400*t₇^17 + 13061332819820635499520*t₇^16
      + 495597440761487627076864*t₇^15 + 12241954915828925988105216*t₇^14
      + 209542498266477588439901184*t₇^13 + 2567861975366128770154398720*t₇^12
      + 22858692514880794412735720448*t₇^11 + 147720485016113073156332706816*t₇^10
      + 680582754613792265106020341248*t₇^9 + 2136574904081347034102547800064*t₇^8
      + 4130075595835818150742871417088*t₇^7 + 3739006082142357309679458650112*t₇^6) * hF

/-- Every noncuspidal rational solution of the fibre-product equation has
one of the four exceptional `t₃`-values. -/
theorem hauptmodulPair_t₃_cases {t₃ t₇ : ℚ}
    (h3 : t₃ ≠ 0) (h7 : t₇ ≠ 0)
    (hpair : HauptmodulPair t₃ t₇) :
    t₃ = -18 ∨ t₃ = -1152 ∨ t₃ = -81 / 2 ∨ t₃ = -81 / 128 := by
  have hF := hauptmodulPair_sub hpair
  have hVd := tVd_ne_zero h7 hF
  have hVd3 : tVd t₃ t₇ ^ 3 ≠ 0 := pow_ne_zero 3 hVd
  have hOn := transfer_on_curve hVd hF
  rcases fullTwo_affine_classification_unconditional hOn with
      ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩ |
        ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩
  · -- (0, 0): forces t₇ = -49/2 and t₃ = -18
    left
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * (54 * t₇ + 1323) = 0 := by
      linear_combination hBh
    have ht₇ : t₇ = -49 / 2 := by
      rcases mul_eq_zero.mp hlin with h | h
      · exact absurd h hVd3
      · linarith
    subst ht₇
    have hVn := transfer_V_cleared hVd hV
    have hfac : (-51883209 / 16 : ℚ) * ((t₃ - 3) * (t₃ + 18)) = 0 := by
      unfold tVn tVd at hVn
      linear_combination hVn
    have hor : t₃ = 3 ∨ t₃ = -18 := by
      rcases mul_eq_zero.mp hfac with h | h
      · norm_num at h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
    rcases hor with rfl | h
    · exfalso
      norm_num at hF
    · exact h
  · -- (9, 0): forces t₇ = -2 and t₃ = -1152
    right; left
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * (3456 * t₇ + 6912) = 0 := by
      linear_combination hBh
    have ht₇ : t₇ = -2 := by
      rcases mul_eq_zero.mp hlin with h | h
      · exact absurd h hVd3
      · linarith
    subst ht₇
    have hVn := transfer_V_cleared hVd hV
    have hfac : ((t₃ + 1152) * (127 * t₃ + 1131) : ℚ) * 144 = 0 := by
      unfold tVn tVd at hVn
      linear_combination hVn
    have hor : t₃ = -1152 ∨ t₃ = -1131 / 127 := by
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      · norm_num at h
    rcases hor with h | rfl
    · exact h
    · exfalso
      norm_num at hF
  · -- (-7, 0): forces t₇ = 0, impossible
    exfalso
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * (128 * t₇) = 0 := by
      linear_combination -hBh
    rcases mul_eq_zero.mp hlin with h | h
    · exact hVd3 h
    · exact h7 (by linarith)
  · -- (-3, 12): the ordinate relation is contradictory
    exfalso
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * 3456 = 0 := by
      linear_combination hBh
    rcases mul_eq_zero.mp hlin with h | h
    · exact hVd3 h
    · norm_num at h
  · -- (-3, -12): the seven-adic resultant forces t₇ = -8, t₃ = -81/128
    right; right; right
    have hVn := transfer_V_cleared hVd hV
    have hS : tVn t₃ t₇ + 3 * tVd t₃ t₇ = 0 := by
      rw [hVn]
      ring
    have hres := resultant_S hS hF
    have ht₇ : t₇ = -8 := by
      have h1 : (186624 : ℚ) * t₇ ^ 6 ≠ 0 := by
        intro h
        rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact h7 (pow_eq_zero_iff (by norm_num) |>.mp h)
      have h2 := pow_ne_zero 4 (MazurTorsion.levelSevenQuadratic_ne_zero t₇)
      have h3 := pow_ne_zero 4 (MazurTorsion.levelSevenQuartic_ne_zero t₇)
      have hfac :
          ((186624 : ℚ) * t₇ ^ 6 * (t₇ + 8)) *
            ((t₇ ^ 2 + 245 * t₇ + 2401) ^ 4 *
              (t₇ ^ 4 - 490 * t₇ ^ 3 - 21609 * t₇ ^ 2 -
                235298 * t₇ - 823543) ^ 4) = 0 := by
        linear_combination hres
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h1
        · linarith
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2
        · exact absurd h h3
    subst ht₇
    have hfac : (12 : ℚ) * ((119 * t₃ + 2607) * (128 * t₃ + 81)) = 0 := by
      have hS' : tVn t₃ (-8) + 3 * tVd t₃ (-8) = 0 := hS
      unfold tVn tVd at hS'
      linear_combination hS'
    have hor : t₃ = -2607 / 119 ∨ t₃ = -81 / 128 := by
      rcases mul_eq_zero.mp hfac with h | h
      · norm_num at h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
    rcases hor with rfl | h
    · exfalso
      norm_num at hF
    · exact h
  · -- (21, 84): forces t₇ = -49/8 and t₃ = -81/2
    right; right; left
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * (27648 * t₇ + 169344) = 0 := by
      linear_combination hBh
    have ht₇ : t₇ = -49 / 8 := by
      rcases mul_eq_zero.mp hlin with h | h
      · exact absurd h hVd3
      · linarith
    subst ht₇
    have hVn := transfer_V_cleared hVd hV
    have hfac : (17294403 / 1024 : ℚ) *
        ((2 * t₃ + 81) * (7 * t₃ + 39)) = 0 := by
      unfold tVn tVd at hVn
      linear_combination hVn
    have hor : t₃ = -81 / 2 ∨ t₃ = -39 / 7 := by
      rcases mul_eq_zero.mp hfac with h | h
      · norm_num at h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
    rcases hor with h | rfl
    · exact h
    · exfalso
      norm_num at hF
  · -- (21, -84): forces t₇ = 0, impossible
    exfalso
    have hBh := transfer_W_cleared hVd hW
    rw [tBh_eq, tCh_eq, transfer_V_cleared hVd hV] at hBh
    have hlin : tVd t₃ t₇ ^ 3 * (27648 * t₇) = 0 := by
      linear_combination hBh
    rcases mul_eq_zero.mp hlin with h | h
    · exact hVd3 h
    · exact h7 (by linarith)

end MazurTorsion.XZeroTwentyOne

end

theorem solution (t₃ t₇ : ℚ) (h3 : t₃ ≠ 0) (h7 : t₇ ≠ 0)
    (hpair : (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 =
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) * (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3) :
    t₃ = -18 ∨ t₃ = -1152 ∨ t₃ = -81 / 2 ∨ t₃ = -81 / 128 :=
  MazurTorsion.XZeroTwentyOne.hauptmodulPair_t₃_cases h3 h7 hpair
#print axioms solution
