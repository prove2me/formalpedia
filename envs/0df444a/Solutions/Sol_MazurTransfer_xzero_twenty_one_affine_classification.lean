-- Prove2me | solution 1 for MazurTransfer.xzero_twenty_one_affine_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T11:17:05.555157+00:00
-- url     : https://prove2.me/submissions/3f8be812-eb7d-4b3d-af07-d57f635863e3

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_good_reduction_card_bound


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

/-- The minimal conductor-`21` Weierstrass model used for `X₀(21)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -4, -1⟩

/-- The full rational two-torsion model obtained by completing the square. -/
def fullTwoCurve : WeierstrassCurve ℚ :=
  ⟨0, -2, 0, -63, 0⟩

instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance fullTwoCurve_isElliptic : fullTwoCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [fullTwoCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]



/-- The affine equation of the full-two-torsion model. -/
def OnFullTwoCurve (V W : ℚ) : Prop :=
  W ^ 2 = V * (V - 9) * (V + 7)



















private lemma commonDivisor_dvd_sixtyThree
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 2 * m * n - 63 * n ^ 2) :
    d ∣ 63 := by
  have hm3 : d ∣ m ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨m * b - (-2 * m - 63 * n) * a, ?_⟩
    linear_combination m * hb - (-2 * m - 63 * n) * ha
  have h63n3 : d ∣ 63 * n ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨(m - 2 * n) * a - n * b, ?_⟩
    linear_combination (m - 2 * n) * ha - n * hb
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h63n3)

/-- If a nonzero factor of a square has gcd dividing `63` with its cofactor,
its squareclass is represented by a signed squarefree divisor of `63`. -/
theorem squareClass_of_gcd_dvd_sixtyThree
    {A B C : ℤ} (hA : A ≠ 0) (hAB : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (63 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
      A = 3 * z ^ 2 ∨ A = -(3 * z ^ 2) ∨
      A = 7 * z ^ 2 ∨ A = -(7 * z ^ 2) ∨
      A = 21 * z ^ 2 ∨ A = -(21 * z ^ 2) := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hAB] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hAB
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hdiv : g.natAbs ∣ 63 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hboundNat : g.natAbs ≤ 63 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hbound : g ≤ 63 := by
    have : (g.natAbs : ℤ) ≤ 63 := by exact_mod_cast hboundNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  have hg :
      g = 1 ∨ g = 3 ∨ g = 7 ∨ g = 9 ∨ g = 21 ∨ g = 63 := by
    interval_cases g <;> norm_num at hdiv
    all_goals simp
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    rcases hg with hg | hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by simpa using hAz)))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (by simpa using hAz)))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by nlinarith [hAz])))))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    rcases hg with hg | hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr
        (Or.inl (by nlinarith [hAz]))))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩

/-- Every nonzero rational abscissa of the split cubic belongs to one of the
eight squareclasses supported at `3` and `7`. -/
theorem abscissa_squareClass
    {V W : ℚ} (hV : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    (∃ r : ℚ, V = r ^ 2) ∨
    (∃ r : ℚ, V = -r ^ 2) ∨
    (∃ r : ℚ, V = 3 * r ^ 2) ∨
    (∃ r : ℚ, V = -(3 * r ^ 2)) ∨
    (∃ r : ℚ, V = 7 * r ^ 2) ∨
    (∃ r : ℚ, V = -(7 * r ^ 2)) ∨
    (∃ r : ℚ, V = 21 * r ^ 2) ∨
    (∃ r : ℚ, V = -(21 * r ^ 2)) := by
  let m : ℤ := V.num
  let n : ℤ := V.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 2 * m * n - 63 * n ^ 2
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast V.den_ne_zero
  have hVmn : V = (m : ℚ) / n :=
    V.num_div_den.symm
  have hscaled : (W * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hVmn] at hcurve
    unfold OnFullTwoCurve at hcurve
    field_simp [hn0] at hcurve
    calc
      (W * n ^ 2) ^ 2 = W ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 - 2 * m * n - 63 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsq : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨W * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hAB : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : A ≠ 0 := by
    apply mul_ne_zero
    · dsimp [m]
      exact Rat.num_ne_zero.mpr hV
    · dsimp [n]
      exact_mod_cast V.den_ne_zero
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den V
  have hgcd : GCDMonoid.gcd A B ∣ (63 : ℤ) :=
    commonDivisor_dvd_sixtyThree hmn
      (GCDMonoid.gcd_dvd_left A B)
      (GCDMonoid.gcd_dvd_right A B)
  have lift :
      ∀ {d z : ℤ}, A = d * z ^ 2 →
        V = (d : ℚ) * ((z : ℚ) / n) ^ 2 := by
    intro d z hd
    rw [hVmn]
    simp only [A] at hd
    field_simp [hn0]
    exact_mod_cast hd
  obtain ⟨z, hz | hz | hz | hz | hz | hz | hz | hz⟩ :=
    squareClass_of_gcd_dvd_sixtyThree hA0 hAB hgcd
  · left
    exact ⟨(z : ℚ) / n, by simpa using lift (d := 1) (by simpa using hz)⟩
  · right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -1) (by nlinarith [hz])⟩
  · right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -3) (by nlinarith [hz])⟩
  · right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -7) (by nlinarith [hz])⟩
  · right; right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; right; right; right; right
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -21) (by nlinarith [hz])⟩

/-- Clearing the denominator of a chosen squareclass produces its primitive
integral homogeneous space. -/
theorem homogeneousSpace_of_squareClass
    (d : ℤ) {V W r : ℚ} (hr : r ≠ 0)
    (hV : V = (d : ℚ) * r ^ 2) (hcurve : OnFullTwoCurve V W) :
    ∃ m n c : ℤ,
      IsCoprime m n ∧ m ≠ 0 ∧ 0 < n ∧
      r = (m : ℚ) / (n : ℚ) ∧
      c ^ 2 =
        d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) := by
  let m : ℤ := r.num
  let n : ℤ := r.den
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hr
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast r.den_pos
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den r
  have hrmn : r = (m : ℚ) / (n : ℚ) :=
    r.num_div_den.symm
  have hscaled :
      (W * (n : ℚ) ^ 3 / (m : ℚ)) ^ 2 =
        ((d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) : ℤ) : ℚ) := by
    unfold OnFullTwoCurve at hcurve
    rw [div_pow, mul_pow, hcurve, hV, hrmn]
    push_cast
    field_simp [hmQ, hnQ]
  have hsquare :
      IsSquare
        (((d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) : ℤ) : ℚ)) :=
    ⟨W * (n : ℚ) ^ 3 / (m : ℚ),
      by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsquare
  refine ⟨m, n, c, hmn, hm0, hnpos, hrmn, ?_⟩
  simpa [pow_two] using hc.symm

private abbrev reduceTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma primitive_has_odd_coordinate
    {m n : ℤ} (hmn : IsCoprime m n) :
    reduceTwo (m : ZMod 16) ≠ 0 ∨ reduceTwo (n : ZMod 16) ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  have hmEven : Even m := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [reduceTwo] using h.1
  have hnEven : Even n := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [reduceTwo] using h.2
  have hunit : IsUnit (2 : ℤ) :=
    hmn.isUnit_of_dvd'
      (even_iff_two_dvd.mp hmEven) (even_iff_two_dvd.mp hnEven)
  norm_num [Int.isUnit_iff] at hunit

private lemma negativeOne_obstruction_mod_sixteen :
    ∀ m n c : ZMod 16,
      (reduceTwo m ≠ 0 ∨ reduceTwo n ≠ 0) →
      c ^ 2 ≠
        (-1) * ((-1) * m ^ 2 - 9 * n ^ 2) *
          ((-1) * m ^ 2 + 7 * n ^ 2) := by
  decide

private lemma three_obstruction_mod_sixteen :
    ∀ m n c : ZMod 16,
      (reduceTwo m ≠ 0 ∨ reduceTwo n ≠ 0) →
      c ^ 2 ≠
        3 * (3 * m ^ 2 - 9 * n ^ 2) *
          (3 * m ^ 2 + 7 * n ^ 2) := by
  decide

/-- The squareclass `-1` is locally impossible. -/
theorem no_negativeOne_squareClass
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = -r ^ 2)
    (hcurve : OnFullTwoCurve V W) : False := by
  obtain ⟨m, n, c, hmn, -, -, -, hc⟩ :=
    homogeneousSpace_of_squareClass (-1) hr
      (by simpa using hV) hcurve
  apply negativeOne_obstruction_mod_sixteen
    (m : ZMod 16) (n : ZMod 16) (c : ZMod 16)
    (primitive_has_odd_coordinate hmn)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) hc

/-- The squareclass `3` is locally impossible. -/
theorem no_three_squareClass
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = 3 * r ^ 2)
    (hcurve : OnFullTwoCurve V W) : False := by
  obtain ⟨m, n, c, hmn, -, -, -, hc⟩ :=
    homogeneousSpace_of_squareClass 3 hr hV hcurve
  apply three_obstruction_mod_sixteen
    (m : ZMod 16) (n : ZMod 16) (c : ZMod 16)
    (primitive_has_odd_coordinate hmn)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) hc

/-- The exact global leaf for squareclass `1`. -/
def PrincipalQuarticClassified : Prop :=
  ∀ m n c : ℤ, IsCoprime m n →
    c ^ 2 = m ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = 9 * n ^ 2

/-- The exact global leaf for squareclass `-3`, after removing the forced
square factor `9`. -/
def NegativeThreeQuarticClassified : Prop :=
  ∀ m n c : ℤ, IsCoprime m n →
    c ^ 2 = -3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2





private lemma normalize_negativeThree_space
    {m n c : ℤ}
    (h : c ^ 2 =
      (-3) * ((-3) * m ^ 2 - 9 * n ^ 2) *
        ((-3) * m ^ 2 + 7 * n ^ 2)) :
    ∃ q : ℤ,
      c = 3 * q ∧
      q ^ 2 = -3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 := by
  have hthree : (3 : ℤ) ∣ c ^ 2 := by
    rw [h]
    refine ⟨3 * (-3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4), ?_⟩
    ring
  have hprime : Prime (3 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by norm_num)
  have hc : (3 : ℤ) ∣ c :=
    hprime.dvd_of_dvd_pow hthree
  obtain ⟨q, hq⟩ := hc
  refine ⟨q, hq, ?_⟩
  have hfactor :
      (-3) * ((-3) * m ^ 2 - 9 * n ^ 2) *
          ((-3) * m ^ 2 + 7 * n ^ 2) =
        9 * (-3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4) := by
    ring
  rw [hfactor] at h
  rw [hq] at h
  nlinarith [h]

/-- Assuming the principal quartic descent, squareclass `1` contains only
the visible two-torsion abscissa `9`. -/
theorem one_squareClass_eq_nine
    (hprincipal : PrincipalQuarticClassified)
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = r ^ 2)
    (hcurve : OnFullTwoCurve V W) :
    V = 9 := by
  obtain ⟨m, n, c, hmn, hm0, hnpos, hrmn, hc⟩ :=
    homogeneousSpace_of_squareClass 1 hr
      (by simpa using hV) hcurve
  have hc' :
      c ^ 2 = m ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 := by
    linear_combination hc
  rcases hprincipal m n c hmn hc' with hm | hn | hmnSq
  · exact absurd hm hm0
  · omega
  · have hmnSqQ : (m : ℚ) ^ 2 = 9 * (n : ℚ) ^ 2 := by
      exact_mod_cast hmnSq
    rw [hV, hrmn]
    field_simp
    nlinarith [hmnSqQ]

/-- Assuming the second quartic descent, squareclass `-3` contains only the
visible order-four abscissa `-3`. -/
theorem negativeThree_squareClass_eq
    (hnegative : NegativeThreeQuarticClassified)
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = -(3 * r ^ 2))
    (hcurve : OnFullTwoCurve V W) :
    V = -3 := by
  obtain ⟨m, n, c, hmn, hm0, hnpos, hrmn, hc⟩ :=
    homogeneousSpace_of_squareClass (-3) hr
      (by simpa using hV) hcurve
  obtain ⟨q, -, hq⟩ := normalize_negativeThree_space hc
  rcases hnegative m n q hmn hq with hm | hn | hmnSq
  · exact absurd hm hm0
  · omega
  · have hmnSqQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
      exact_mod_cast hmnSq
    rw [hV, hrmn]
    field_simp
    nlinarith [hmnSqQ]

/-- Translation by the rational two-torsion point `(0,0)`, on coordinates. -/
theorem translate_by_zero_twoTorsion
    {V W : ℚ} (hV : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    OnFullTwoCurve (-63 / V) (63 * W / V ^ 2) := by
  unfold OnFullTwoCurve at hcurve ⊢
  field_simp
  linear_combination (63 : ℚ) * hcurve

/-- Conditional rank-zero statement for the split model.  Its hypotheses are
exactly the two everywhere-locally-soluble quartic descents isolated above. -/
theorem abscissa_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    V = 0 ∨ V = 9 ∨ V = -7 ∨ V = -3 ∨ V = 21 := by
  by_cases hV0 : V = 0
  · exact Or.inl hV0
  have hinv := translate_by_zero_twoTorsion hV0 hcurve
  rcases abscissa_squareClass hV0 hcurve with
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ |
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact Or.inr (Or.inl
      (one_squareClass_eq_nine hprincipal hr hc hcurve))
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact (no_negativeOne_squareClass hr hc hcurve).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact (no_three_squareClass hr hc hcurve).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (negativeThree_squareClass_eq hnegative hr hc hcurve))))
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact (no_negativeOne_squareClass hr' hc' hinv).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = (3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    have h9 :=
      one_squareClass_eq_nine hprincipal hr' hc' hinv
    right; right; left
    field_simp at h9
    linarith
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 * (1 / r) ^ 2) := by
      rw [hc]
      field_simp
      ring
    have hneg :=
      negativeThree_squareClass_eq hnegative hr' hc' hinv
    right; right; right; right
    field_simp at hneg
    linarith
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = 3 * (1 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact (no_three_squareClass hr' hc' hinv).elim



/-- Conditional classification of all affine solutions on the split model.
Together with the point at infinity, these are the eight expected rational
points. -/
theorem fullTwo_affine_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) := by
  rcases abscissa_classification hprincipal hnegative hcurve with
      hV | hV | hV | hV | hV
  · left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · right; left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · right; right; left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    have hfac : (W - 12) * (W + 12) = 0 := by
      nlinarith [hcurve]
    rcases mul_eq_zero.mp hfac with hW | hW
    · right; right; right; left
      exact ⟨hV, by linarith⟩
    · right; right; right; right; left
      exact ⟨hV, by linarith⟩
  · rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    have hfac : (W - 84) * (W + 84) = 0 := by
      nlinarith [hcurve]
    rcases mul_eq_zero.mp hfac with hW | hW
    · right; right; right; right; right; left
      exact ⟨hV, by linarith⟩
    · right; right; right; right; right; right
      exact ⟨hV, by linarith⟩



end MazurTorsion.XZeroTwentyOne

end


/- Source module: EllipticCurves.Mathlib.EllipticCurvePoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance instDecidableEquationOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance instDecidableNonsingularOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm

instance instFinitePoint [Finite R] : Finite W'.Point :=
  .of_equiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

instance instFintypePointOfDecidableEq [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

section PointMap

variable {K : Type*} [Field K] (W : Affine K)



variable [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves. -/
def Point.congr {W₁ W₂ : Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h
  exact AddEquiv.refl _





variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]











end PointMap

namespace Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (σ : F ≃ₐ[S] K)

/-- The group isomorphism on nonsingular points induced by an algebra isomorphism
`σ : F ≃ₐ[S] K`, where `W` is defined over a subring of a ring `S`, and `F` and `K` are field
extensions of `S`; the equiv version of `WeierstrassCurve.Affine.Point.map`. -/
noncomputable def mapEquiv : (W'⁄F).Point ≃+ (W'⁄K).Point where
  toFun := map (σ : F →ₐ[S] K)
  invFun := map (σ.symm : K →ₐ[S] F)
  map_add' := map_add _
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.symm_apply_apply x, σ.symm_apply_apply y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.apply_symm_apply x, σ.apply_symm_apply y⟩

@[simp] lemma coe_mapEquiv : ⇑(mapEquiv (W' := W') σ) = ⇑(map (W' := W') (σ : F →ₐ[S] K)) :=
  rfl

end Point

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTransfer.FinitePointReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open scoped WeierstrassCurve.Affine
namespace MazurTransfer

/-- Boundary: identify a finite rational point group with its full torsion
subgroup. Downstream consumers: the X_1(14), X_1(15), and X_0(21) point counts. -/
noncomputable def finitePointTorsionEquiv (E : WeierstrassCurve ℚ)
    [Finite (E⁄ℚ).Point] : (E⁄ℚ).Point ≃+ MazurCampaign.RationalTorsion E :=
  (AddEquiv.ofBijective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
    ⟨Subtype.val_injective, fun P => ⟨⟨P, isOfFinAddOrder_of_finite P⟩, rfl⟩⟩).symm

lemma finite_point_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite ((W.map (Int.castRingHom ℚ))⁄ℚ).Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card ((W.map (Int.castRingHom ℚ))⁄ℚ).Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  rw [Nat.card_congr (finitePointTorsionEquiv (W.map (Int.castRingHom ℚ))).toEquiv]
  exact (MazurCampaign.good_reduction_card_bound W p hp hgood).2

lemma finite_toAffine_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite (W.map (Int.castRingHom ℚ)).toAffine.Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card (W.map (Int.castRingHom ℚ)).toAffine.Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  let E := W.map (Int.castRingHom ℚ)
  let e : (E⁄ℚ).Point ≃+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.congr (by
      ext <;> simp [E, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.map])
  letI : Finite (E⁄ℚ).Point := Finite.of_equiv E.toAffine.Point e.symm.toEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact finite_point_card_dvd W p hp hgood

end MazurTransfer
#print axioms MazurTransfer.finite_point_card_dvd

end


/- Source module: MazurTorsion.NumberTheory.RatNorthcott. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Northcott's property for the rational logarithmic height

The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its normalized numerator and its positive denominator. Consequently, a height bound
places the numerator and denominator in finite integer intervals. This file records that elementary
rational specialization of Northcott's theorem.
-/

section

namespace MazurTorsion

open Height

/-- The rational numbers of logarithmic height at most `B` form a finite set. -/
theorem finite_rat_logHeight₁_le (B : ℝ) :
    {q : ℚ | logHeight₁ q ≤ B}.Finite := by
  let N := Nat.ceil (Real.exp B)
  let encode : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  let box : Set (ℤ × ℕ) :=
    Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc 0 N
  have hbox : box.Finite := by
    exact (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Icc 0 N)
  have himage : encode '' {q : ℚ | logHeight₁ q ≤ B} ⊆ box := by
    rintro p ⟨q, hq, rfl⟩
    have hmax_real : (max q.num.natAbs q.den : ℝ) ≤ Real.exp B := by
      apply Real.le_exp_of_log_le
      simpa only [Set.mem_setOf_eq, Rat.logHeight₁_eq_log_max, Nat.cast_max] using hq
    have hmax_cast : (max q.num.natAbs q.den : ℝ) ≤ (N : ℝ) :=
      hmax_real.trans (Nat.le_ceil (Real.exp B))
    have hmax : max q.num.natAbs q.den ≤ N := by
      exact_mod_cast hmax_cast
    have hnum : q.num.natAbs ≤ N := le_trans (le_max_left _ _) hmax
    have hden : q.den ≤ N := le_trans (le_max_right _ _) hmax
    have hnum_upper : q.num ≤ (N : ℤ) := by
      exact Int.le_natAbs.trans (Int.ofNat_le.mpr hnum)
    have hnum_lower : -(N : ℤ) ≤ q.num := by
      have hneg : -q.num ≤ (N : ℤ) :=
        Int.le_natAbs.trans (by simpa only [Int.natAbs_neg] using Int.ofNat_le.mpr hnum)
      omega
    exact ⟨⟨hnum_lower, hnum_upper⟩, ⟨Nat.zero_le _, hden⟩⟩
  refine Set.Finite.of_finite_image (hbox.subset himage) ?_
  intro q _ r _ h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The usual logarithmic height on `ℚ` has Northcott's property. -/
instance rationalLogHeightNorthcott : Northcott (logHeight₁ (K := ℚ)) where
  finite_le := finite_rat_logHeight₁_le

end MazurTorsion

end
end


/- Source module: MazurTorsion.Foundations.NaiveHeightDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin
-/



/-!
# Naïve-height descent for rational elliptic curves

This file is a narrow port of the height part of Michael Stoll's
`EllipticCurves/MordellWeil.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It proves the approximate parallelogram law for the naïve logarithmic
height on affine Weierstrass points. Combined with Northcott and finite
index of multiplication by two or three, this gives finite generation by
the descent theorems in `Mathlib.GroupTheory.Descent`.

The much larger weak Mordell--Weil and Selmer-group layers are deliberately
not imported: callers may establish the required finite index by a
curve-specific descent.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]
  {W' : WeierstrassCurve R}

open MvPolynomial Nat

lemma den_duplication_eq {x y : R} (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ =
      (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have heq := (W'.toAffine.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R}
    (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔
      y = W'.toAffine.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff,
    WeierstrassCurve.Affine.negY]
  grind only

variable {F : Type*} [Field F]
  {W : WeierstrassCurve F}

lemma den_duplication_ne_zero_or_num_duplication_ne_zero
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.toAffine.nonsingular_iff x y).mp h
  rw [W.toAffine.equation_iff x y] at h₁
  by_cases hzero : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
      grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! hzero
    rw [b₂, b₄, b₆] at hzero
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.toAffine.Equation x y)
    (hn : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (ha : a ≠ 0) :
      a ^ 2 * (b * (c / a)) = a * b * c := by
    field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', WeierstrassCurve.Affine.addX,
    sub_sub, sub_sub, mul_sub, mul_add]
  simp only [WeierstrassCurve.Affine.slope, ↓reduceIte, hn]
  rw [WeierstrassCurve.Affine.negY,
    show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring,
    div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.toAffine.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
    W.toAffine.addX xP xQ (W.toAffine.slope xP xQ yP yQ) =
      ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
        (xP - xQ) ^ 2 := by
  have hxPQ : xP - xQ ≠ 0 := by
    grind only
  simp [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.slope, hn, div_pow]
  field

lemma Point.xRep_add_self_of_Y_ne {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hn : y ≠ W.toAffine.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]



lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some,
    addX_of_X_ne hn]

lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 +
            W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn,
    xRep_some, addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) :
    {P : W.toAffine.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty
      {P : W.toAffine.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by
    ext
    simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) :
    {P : W.toAffine.Point | P.xRep 0 = x}.Finite := by
  have hsubset :
      {P : W.toAffine.Point | P.xRep 0 = x} ⊆
        {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset hsubset

lemma Point.sym2x_eq (P Q : W.toAffine.Point) :
    P.sym2x Q =
      ![P.xRep 0 * Q.xRep 0,
        P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
        P.xRep 1 * Q.xRep 1] :=
  rfl

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.toAffine.Point) :
    Point.sym2x P P =
      fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [Point.sym2x_zero_zero, succ_eq_add_one, reduceAdd,
      addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp
  | some .. =>
    simp only [Point.sym2x_some_some, succ_eq_add_one, reduceAdd,
      Point.sym2x_some_zero, addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + P) 0 =
        fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, Point.sym2x_zero_zero, one_smul, addSubMap]
    ext i
    fin_cases i <;> simp
  | some x y h =>
    have heq := (W.toAffine.equation_iff x y).mp h.1
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [hrs]
    by_cases hvertical : y = W.toAffine.negY x y
    · have hden := (den_duplication_eq_zero_iff h.1).mpr hvertical
      rw [hden, add_self_of_Y_eq hvertical, Point.sym2x_zero_zero]
      refine ⟨_,
        den_duplication_ne_zero_or_num_duplication_ne_zero h
          |>.neg_resolve_left hden, ?_⟩
      simp
    · have hden := (den_duplication_eq_zero_iff h.1).not.mpr hvertical
      refine ⟨_, hden, ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h hvertical,
        mul_div_cancel₀ _ hden]

theorem Point.sym2x_add_sub_eq_addSubMap_sym2x
    (P Q : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + Q) (P - Q) =
        fun i ↦ (addSubMap W i).eval <| Point.sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [Point.sym2x_neg_right, Point.sym2x_comm 0] using
      P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>
    exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [Point.sym2x_neg_right, Point.sym2x_comm _ Q] using
      Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun heq ↦ by
      grind only [X_eq_iff.mp heq]
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some xP yP hP).sym2x (some xQ yQ hQ)) =
          ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) -
              W.b₆ * (xP + xQ) - W.b₈,
            2 * (xP + xQ) * (xP * xQ) +
              W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
            (xP - xQ) ^ 2] := by
      ext i
      fin_cases i <;> simp [addSubMap]
      ring
    have hsub : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 hsub, ?_⟩
    have heqP := (W.toAffine.equation_iff xP yP).mp hP.1
    have heqQ := (W.toAffine.equation_iff xQ yQ).mp hQ.1
    rw [hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i
    fin_cases i <;> simp [field] <;> grobner

end Decidable

section Height

open Height

variable [AdmissibleAbsValues F]

/-- The logarithmic projective height of an affine point's `x`-coordinates. -/
noncomputable def Point.naiveHeight (P : W.toAffine.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.toAffine.Point) :
    P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.toAffine.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. =>
    simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight,
    Point.sym2x_eq]
  have hmul := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have hvec (v : Fin 2 → F) : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> simp
  have hzero (P : W.toAffine.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 :=
    hvec P.xRep ▸ P.xRep_ne_zero
  specialize hC (hzero P) (hzero Q)
  rw [hvec P.xRep, hvec Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |(P + Q).naiveHeight + (P - Q).naiveHeight -
          2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ :=
    WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ :=
    Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

instance [Northcott (logHeight₁ (K := F))] :
    Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  letI : Filter.TendstoCofinite (fun P : W.toAffine.Point ↦ P.xRep 0) :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 fun x ↦ by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        (finite_preimage_xRep0 (W := W) x)
  exact Northcott.comp_of_finite_fibers
    (h := fun P : W.toAffine.Point ↦ P.xRep 0)
    (h' := logHeight₁)

variable [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F]

theorem fg_point_of_finiteIndex_two
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  have hnonneg (P : W.toAffine.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' hindex hnonneg hC



end Height

end WeierstrassCurve.Affine

end


/- Source module: MazurTorsion.Foundations.TwoTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/



/-!
# Rational two-torsion bounds

This file bounds the two-torsion of a Weierstrass curve in characteristic
different from two and excludes an elementary abelian subgroup of order eight.
These are elementary structural inputs to the torsion classification in
Mazur's theorem.
-/

namespace MazurTorsion

open scoped WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [NeZero (2 : F)]

noncomputable section

private noncomputable def twoTorsionRootMap :
    {P : (E⁄F).Point // (2 : ℕ) • P = 0} →
      Option (E.twoTorsionPolynomial.toPoly.rootSet F)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y h, htwo⟩ => some ⟨x, by
      rw [Polynomial.mem_rootSet_of_ne]
      · simp only [Polynomial.aeval_def]
        rw [Algebra.algebraMap_self, Polynomial.eval₂_id]
        have hneg : WeierstrassCurve.Affine.Point.some x y h =
            -WeierstrassCurve.Affine.Point.some x y h := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        have hy : y = (E⁄F).negY x y := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq, true_and] using hneg
        have heq := h.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [WeierstrassCurve.Affine.negY] at hy
        change y = -y - E.a₁ * x - E.a₃ at hy
        change y ^ 2 + E.a₁ * x * y + E.a₃ * y =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ at heq
        have hlin : 2 * y + E.a₁ * x + E.a₃ = 0 := by
          linear_combination hy
        simp only [Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆]
        linear_combination -4 * heq +
          (2 * y + E.a₁ * x + E.a₃) * hlin
      · intro hp
        have hdeg :
            E.twoTorsionPolynomial.toPoly.natDegree = 3 :=
          Cubic.natDegree_of_a_ne_zero' (by
            rw [show (4 : F) = 2 ^ 2 by norm_num]
            exact pow_ne_zero 2 (NeZero.ne (2 : F)))
        rw [hp, Polynomial.natDegree_zero] at hdeg
        omega⟩

private theorem twoTorsionRootMap_injective :
    Function.Injective (twoTorsionRootMap E) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [twoTorsionRootMap] at h
  | some x y hxy =>
      cases Q with
      | zero => simp [twoTorsionRootMap] at h
      | some x' y' hxy' =>
          simp only [twoTorsionRootMap, Option.some.injEq,
            Subtype.mk.injEq] at h
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x' y' hxy').xRep := by
            simp [h]
          rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hself :
                WeierstrassCurve.Affine.Point.some x' y' hxy' =
                  -WeierstrassCurve.Affine.Point.some x' y' hxy' := by
              rw [← add_eq_zero_iff_eq_neg]
              simpa [two_nsmul] using hQ
            rw [hself.symm] at heq
            exact heq

/-- The points killed by `2` form a finite type in characteristic different
from two. -/
theorem finite_two_torsion :
    Finite {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
  Finite.of_injective (twoTorsionRootMap E)
    (twoTorsionRootMap_injective E)



















end

end MazurTorsion

end


/- Source module: MazurTorsion.GroupTheory.IndexNSmulFG. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/



/-!
# The index of multiplication on a finitely generated abelian group

This file is a narrow port of the finitely-generated-abelian-group part of
Michael Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It extends `AddSubgroup.index_range_nsmul`, which treats a finite free
`ℤ`-module, to a finitely generated commutative group with torsion.  The
result will let a curve-specific two-descent turn a bound on
`E(ℚ) / 2 E(ℚ)` into a bound on the Mordell--Weil rank.
-/

/-- First-isomorphism counting: the cardinality of an additive group is the
cardinality of the kernel times the cardinality of the range of a homomorphism. -/
theorem AddMonoidHom.card_ker_mul_card_range {G H : Type*}
    [AddGroup G] [AddGroup H] (φ : G →+ H) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm,
    mul_comm]
  exact
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- On a finite additive group, the index of the range of an endomorphism
equals the cardinality of its kernel. -/
theorem AddMonoidHom.index_range_eq_card_ker {G : Type*}
    [AddGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h1 : φ.range.index * Nat.card φ.range = Nat.card G :=
    φ.range.index_mul_card
  exact
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (h1.trans φ.card_ker_mul_card_range.symm)

/-- An additive equivalence maps the kernel of multiplication by `n` onto
the corresponding kernel. -/
lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- Multiplication by `n` on a product has the product of the two ranges as
its range. -/
lemma nsmulAddMonoidHom_range_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod
        (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
    AddSubgroup.mem_prod]
  exact
    ⟨fun ⟨y, hy⟩ ↦
        ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Multiplication by `n` on a product has the product of the two kernels as
its kernel. -/
lemma nsmulAddMonoidHom_ker_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod
        (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- A finite module over a characteristic-zero ring has rank zero. -/
lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦
    ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
      by
        rw [Nat.cast_smul_eq_nsmul]
        exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in
/-- The index of `nG` in a finitely generated commutative group `G` is
`n ^ rank(G)` times the cardinality of its `n`-torsion subgroup. -/
theorem AddSubgroup.index_range_nsmul_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G *
        Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) :=
    ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom
          (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using
        (AddSubgroup.index_map_equiv
          (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker :
      Nat.card (nsmulAddMonoidHom (α := G) n).ker =
        Nat.card
          (nsmulAddMonoidHom
            (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective _
          eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 :
        Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π :=
        LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
        with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 :
            LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun := fun x ↦ x.1.2
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            invFun := fun t ↦ ⟨(0, t), rfl⟩
            left_inv := fun x ↦
              Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv := fun _ ↦ rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker,
        LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 :
        finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul,
    AddMonoidHom.index_range_eq_card_ker,
    nsmulAddMonoidHom_ker_prod,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end


/- Source module: MazurTorsion.NumberTheory.XZeroTwentyOneRankZero. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rank zero for the split `X₀(21)` model

`XZeroTwentyOneDescent` reduces the abscissa classification on

`W² = V(V - 9)(V + 7)`

to two quartic leaves.  This file replaces those leaves by a complete
two-isogeny descent.  The two-isogenous curve is

`Y² = X(X² + 4X + 256)`,

and every nonzero rational abscissa on it is a rational square: the
negative squareclasses are impossible by positivity, and the squareclass
`2` dies by an explicit two-adic descent.  Consequently a rational point of
the split model whose abscissa is a square is divisible by two, by the same
explicit reverse-doubling calculation as on the `X₁(14)` model.

The four surviving squareclasses `1`, `-3`, `-7`, `21` then produce four
explicit doubling cosets with representatives

`0`, `(0,0)`, `(-3,12)`, `(21,84)`.

Since the model has full rational two-torsion, the finitely generated index
formula forces Mordell--Weil rank zero, and the rational point group is
finite.
-/

namespace MazurTorsion.XZeroTwentyOne

/-! ## The affine equation and its nonsingular points -/

lemma fullTwoCurve_equation_of_nonsingular
    {U V : ℚ} (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 - 2 * U - 63) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [fullTwoCurve] at heq
  nlinarith [heq]

lemma onFullTwoCurve_of_nonsingular
    {U V : ℚ} (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    OnFullTwoCurve U V := by
  have h := fullTwoCurve_equation_of_nonsingular hP
  unfold OnFullTwoCurve
  linear_combination h

lemma nonsingular_of_onFullTwoCurve
    {U V : ℚ} (h : OnFullTwoCurve U V) :
    fullTwoCurve.toAffine.Nonsingular U V := by
  apply fullTwoCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold OnFullTwoCurve at h
  norm_num [fullTwoCurve]
  linear_combination h

/-! ## The squareclass `2` on the dual curve is impossible

The dual curve is `Y² = X(X² + 4X + 256)`.  An abscissa `X = 2z²` leads,
after clearing denominators, to the primitive integral equation
`c² = 2(m⁴ + 2m²n² + 64n⁴)`, which dies by a short two-adic descent. -/

private abbrev reduceTwoOfFour : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

private lemma odd_leaf_obstruction :
    ∀ μ n c : ZMod 4,
      reduceTwoOfFour μ ≠ 0 → reduceTwoOfFour n ≠ 0 →
      c ^ 2 ≠ 2 * μ ^ 4 + μ ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  decide

private lemma even_leaf_obstruction :
    ∀ ν n c : ZMod 4,
      reduceTwoOfFour n ≠ 0 →
      c ^ 2 ≠ 8 * ν ^ 4 + ν ^ 2 * n ^ 2 + 2 * n ^ 4 := by
  decide

private lemma intCast_reduceTwoOfFour_ne_zero
    {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    reduceTwoOfFour (m : ZMod 4) ≠ 0 := by
  intro h
  apply hm
  have : ((m : ZMod 2) : ZMod 2) = 0 := by
    simpa [reduceTwoOfFour] using h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this

private lemma two_dvd_of_two_dvd_sq {c : ℤ} (h : (2 : ℤ) ∣ c ^ 2) :
    (2 : ℤ) ∣ c :=
  (Int.Prime.dvd_pow' (by norm_num) h)

/-- The primitive integral quartic attached to the dual squareclass `2`
has no solution. -/
private lemma no_dual_two_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ 2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) := by
  intro hc
  have hc2 : (2 : ℤ) ∣ c := by
    apply two_dvd_of_two_dvd_sq
    exact ⟨m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4, hc⟩
  obtain ⟨c₁, rfl⟩ := hc2
  have hc₁ : 2 * c₁ ^ 2 = m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4 := by
    nlinarith [hc]
  have hm2 : (2 : ℤ) ∣ m := by
    by_contra hodd
    have h1 : (m : ZMod 4) ^ 4 + 2 * (m : ZMod 4) ^ 2 * (n : ZMod 4) ^ 2 +
        64 * (n : ZMod 4) ^ 4 = 2 * (c₁ : ZMod 4) ^ 2 := by
      have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₁
      push_cast at this
      linear_combination -this
    have hmu : reduceTwoOfFour (m : ZMod 4) ≠ 0 :=
      intCast_reduceTwoOfFour_ne_zero hodd
    -- modulo four the equation forces `2c₁² = m⁴ + 2m²n²`, odd `m` gives
    -- `2 ∈ {c² - stuff}`, impossible; we discharge by a small decision.
    revert h1
    have : ∀ M N C : ZMod 4, reduceTwoOfFour M ≠ 0 →
        M ^ 4 + 2 * M ^ 2 * N ^ 2 + 64 * N ^ 4 ≠ 2 * C ^ 2 := by
      decide
    exact this _ _ _ hmu
  obtain ⟨μ, rfl⟩ := hm2
  have hn_odd : ¬ (2 : ℤ) ∣ n := by
    intro hn
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' ⟨μ, rfl⟩ hn
    norm_num [Int.isUnit_iff] at this
  have hc₂eq : c₁ ^ 2 = 8 * μ ^ 4 + 4 * μ ^ 2 * n ^ 2 + 32 * n ^ 4 := by
    nlinarith [hc₁]
  have hc₁2 : (2 : ℤ) ∣ c₁ := by
    apply two_dvd_of_two_dvd_sq
    exact ⟨4 * μ ^ 4 + 2 * μ ^ 2 * n ^ 2 + 16 * n ^ 4, by linarith [hc₂eq]⟩
  obtain ⟨c₂, rfl⟩ := hc₁2
  have hc₂ : c₂ ^ 2 = 2 * μ ^ 4 + μ ^ 2 * n ^ 2 + 8 * n ^ 4 := by
    nlinarith [hc₂eq]
  by_cases hμ : (2 : ℤ) ∣ μ
  · obtain ⟨ν, rfl⟩ := hμ
    have hc₃eq : c₂ ^ 2 = 32 * ν ^ 4 + 4 * ν ^ 2 * n ^ 2 + 8 * n ^ 4 := by
      nlinarith [hc₂]
    have hc₂2 : (2 : ℤ) ∣ c₂ := by
      apply two_dvd_of_two_dvd_sq
      exact ⟨16 * ν ^ 4 + 2 * ν ^ 2 * n ^ 2 + 4 * n ^ 4, by linarith [hc₃eq]⟩
    obtain ⟨c₃, rfl⟩ := hc₂2
    have hc₃ : c₃ ^ 2 = 8 * ν ^ 4 + ν ^ 2 * n ^ 2 + 2 * n ^ 4 := by
      nlinarith [hc₃eq]
    apply even_leaf_obstruction (ν : ZMod 4) (n : ZMod 4) (c₃ : ZMod 4)
      (intCast_reduceTwoOfFour_ne_zero hn_odd)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₃
    push_cast at this
    linear_combination this
  · apply odd_leaf_obstruction (μ : ZMod 4) (n : ZMod 4) (c₂ : ZMod 4)
      (intCast_reduceTwoOfFour_ne_zero hμ)
      (intCast_reduceTwoOfFour_ne_zero hn_odd)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₂
    push_cast at this
    linear_combination this

/-- The rational quartic attached to the dual squareclass `2` has no
solution. -/
private lemma no_dual_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * (z ^ 4 + 2 * z ^ 2 + 64) := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    nlinarith [hq]
  have hsq :
      IsSquare ((2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_dual_two_class_int hmn (by simpa [pow_two] using hc.symm)

/-! ## Every nonzero dual abscissa is a square -/

private lemma common_divisor_dual_dvd_256
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 4 * m * n + 256 * n ^ 2) :
    d ∣ 256 := by
  have hm3 : d ∣ m ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨m * b - (4 * m + 256 * n) * a, ?_⟩
    linear_combination m * hb - (4 * m + 256 * n) * ha
  have h256n3 : d ∣ 256 * n ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨n * b - (m + 4 * n) * a, ?_⟩
    linear_combination n * hb - (m + 4 * n) * ha
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h256n3)

/-- A nonzero factor of a square whose gcd with the cofactor divides `256`
has squareclass `±1` or `±2`. -/
private lemma squareclass_of_gcd_dvd_256
    {A B C : ℤ} (hA : A ≠ 0) (hAB : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (256 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
      A = 2 * z ^ 2 ∨ A = -(2 * z ^ 2) := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hAB] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hAB
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hdivNat : g.natAbs ∣ 256 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hdivNat' : g.natAbs ∣ 2 ^ 8 := by
    have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    rwa [h256] at hdivNat
  obtain ⟨k, hk_le, hk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdivNat'
  have hgk : g = 2 ^ k := by
    have : (g.natAbs : ℤ) = ((2 : ℕ) ^ k : ℕ) := by exact_mod_cast hk
    rw [Int.natCast_natAbs, abs_of_pos hgpos] at this
    simpa using this
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · -- `A = g z²` with `g = 2^k`
    have hAz : A = 2 ^ k * z ^ 2 := by rw [← hga, hz, hgk]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨2 ^ j * z, Or.inl ?_⟩
      rw [hAz, hj]
      ring
    · refine ⟨2 ^ j * z, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [hAz, hj]
      ring
  · have hAz : A = -(2 ^ k * z ^ 2) := by rw [← hga, hz, hgk]; ring
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨2 ^ j * z, Or.inr (Or.inl ?_)⟩
      rw [hAz, hj]
      ring
    · refine ⟨2 ^ j * z, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [hAz, hj]
      ring

/-- On the two-isogenous curve `Y² = X(X² + 4X + 256)`, every nonzero
rational abscissa is a square. -/
theorem dual_abscissa_isSquare
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hdual : Y ^ 2 = X * (X ^ 2 + 4 * X + 256)) :
    IsSquare X := by
  -- positivity: a negative abscissa is impossible
  have hXpos : 0 < X := by
    rcases lt_or_gt_of_ne hX0 with hneg | hpos
    · exfalso
      nlinarith [sq_nonneg Y, sq_nonneg (X + 2), hdual]
    · exact hpos
  -- clear denominators
  let m : ℤ := X.num
  let n : ℤ := X.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hX : X = (m : ℚ) / (n : ℚ) := X.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hX0
  have hscaled :
      (Y * (n : ℚ) ^ 2) ^ 2 =
        (((m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) : ℤ) : ℚ) := by
    rw [hX] at hdual
    push_cast
    field_simp at hdual
    linear_combination (n : ℚ) * hdual
  have hsq :
      IsSquare
        (((m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) : ℤ) : ℚ) :=
    ⟨Y * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hAB : (m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : m * n ≠ 0 := by
    apply mul_ne_zero hm0
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hgcd : GCDMonoid.gcd (m * n) (m ^ 2 + 4 * m * n + 256 * n ^ 2) ∣
      (256 : ℤ) :=
    common_divisor_dual_dvd_256 hmn
      (GCDMonoid.gcd_dvd_left _ _)
      (GCDMonoid.gcd_dvd_right _ _)
  obtain ⟨z, hz | hz | hz | hz⟩ :=
    squareclass_of_gcd_dvd_256 hA0 hAB hgcd
  · -- squareclass 1: `X = (z/n)²`
    refine ⟨(z : ℚ) / (n : ℚ), ?_⟩
    rw [hX]
    have hzQ : ((m : ℚ) * n) = (z : ℚ) ^ 2 := by exact_mod_cast hz
    field_simp
    nlinarith [hzQ]
  · -- squareclass -1 contradicts positivity
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hz2 : 0 < z ^ 2 :=
      lt_of_le_of_ne (sq_nonneg z) (Ne.symm (pow_ne_zero 2 hz0))
    have hmnneg : m * n < 0 := by
      rw [hz]
      linarith
    have hnposZ : (0 : ℤ) < n := by
      dsimp [n]
      exact_mod_cast X.den_pos
    have hmneg : m < 0 := by nlinarith [hmnneg, hnposZ]
    have hXneg : X < 0 := by
      rw [hX]
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hmneg
      · exact_mod_cast hnposZ
    linarith
  · -- squareclass 2 dies by the two-adic quartic
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hXval : X = 2 * ((z : ℚ) / n) ^ 2 := by
      rw [hX]
      have hzQ : ((m : ℚ) * n) = 2 * (z : ℚ) ^ 2 := by exact_mod_cast hz
      field_simp
      nlinarith [hzQ]
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (Y / (2 * r)) ^ 2 = 2 * (r ^ 4 + 2 * r ^ 2 + 64) := by
      rw [div_pow]
      rw [hXval] at hdual
      field_simp [hr0]
      nlinarith [hdual]
    exact no_dual_two_class_rat r (Y / (2 * r)) hq
  · -- squareclass -2 contradicts positivity
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hz2 : 0 < z ^ 2 :=
      lt_of_le_of_ne (sq_nonneg z) (Ne.symm (pow_ne_zero 2 hz0))
    have hmnneg : m * n < 0 := by
      rw [hz]
      linarith
    have hnposZ : (0 : ℤ) < n := by
      dsimp [n]
      exact_mod_cast X.den_pos
    have hmneg : m < 0 := by nlinarith [hmnneg, hnposZ]
    have hXneg : X < 0 := by
      rw [hX]
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hmneg
      · exact_mod_cast hnposZ
    linarith

/-! ## Reverse doubling from a square abscissa -/

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = 1 + X / 2 - Y / (2 * q)) :
    Y = q * (X + 2 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X + 2 - 2 * v))
    (hXv : X * v = v ^ 2 - 2 * v - 63) :
    Y = -q * (v ^ 2 + 63) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 + 63) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 + 63) ^ 2 := by
  rw [hY]
  field_simp [hv0]

/-- A nonzero rational point of the split model whose abscissa is a square
is divisible by two.  The proof is an explicit reverse-doubling
calculation through the two-isogenous curve. -/
theorem double_of_square_abscissa
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hUSquare : IsSquare U) :
    ∃ Q : fullTwoCurve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  obtain ⟨s, hs⟩ := hUSquare
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve : V ^ 2 = U * (U ^ 2 - 2 * U - 63) :=
    fullTwoCurve_equation_of_nonsingular hP
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 - 2 * U - 63 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X : ℚ := 2 * U - 2 - 2 * t
  let X' : ℚ := 2 * U - 2 + 2 * t
  have hXprod : X * X' = 256 := by
    dsimp [X, X']
    nlinarith [ht]
  have hX0 : X ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  have hdualFactor :
      X ^ 2 + 4 * X + 256 = 4 * U * X := by
    dsimp [X]
    nlinarith [ht]
  let Y : ℚ := 2 * s * X
  have hdual :
      Y ^ 2 = X * (X ^ 2 + 4 * X + 256) := by
    rw [hdualFactor]
    dsimp [Y]
    rw [hU]
    ring
  obtain ⟨q, hq⟩ := dual_abscissa_isSquare hX0 hdual
  have hXq : X = q ^ 2 := by
    simpa [pow_two] using hq
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 + 4 * X + 256 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdual, hXq]
  let v : ℚ := 1 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = 1 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 - 2 * v - 63 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 - 2 * v - 63) := by
    rw [hwdef, ← hXv, hXq]
    ring
  have hQ : fullTwoCurve.toAffine.Nonsingular v w := by
    apply fullTwoCurve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [fullTwoCurve]
    linear_combination hcurveQ
  have hwneneg : w ≠ -w := by
    intro h
    apply hw0
    linarith
  have hneg : w ≠ fullTwoCurve.toAffine.negY v w := by
    simp only [WeierstrassCurve.Affine.negY]
    norm_num [fullTwoCurve]
    exact hwneneg
  let Q : fullTwoCurve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some v w hQ
  have hdouble :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (h₁ := hQ) hneg
  have hslope :
      fullTwoCurve.toAffine.slope v v w w =
        (3 * v ^ 2 - 4 * v - 63) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, fullTwoCurve, hwneneg]
    ring
  have haddX :
      fullTwoCurve.toAffine.addX v v
          (fullTwoCurve.toAffine.slope v v w w) =
        (v ^ 2 + 63) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 + 63) / v :=
    y_formula_of_reverse_linear hv0
      (y_linear_of_reverse_definition hq0 hvdef) hXv
  have haddXeq :
      fullTwoCurve.toAffine.addX v v
          (fullTwoCurve.toAffine.slope v v w w) = U := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * U * X ^ 2 := by
      dsimp [Y]
      rw [hU]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 =
          q ^ 2 * (v ^ 2 + 63) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 + 63) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 + 63) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 + 63) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 + 63) ^ 2 =
            4 * U * q ^ 2 * v ^ 2 := hcancelled
        _ = 4 * w ^ 2 * U := by rw [hwdef]; ring
    rw [htarget]
    field_simp [hw0]
  have hXcoord :
      Q + Q =
          WeierstrassCurve.Affine.Point.some U V hP ∨
        Q + Q =
          -WeierstrassCurve.Affine.Point.some U V hP := by
    rw [hdouble]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    exact haddXeq
  rcases hXcoord with hQQ | hQQ
  · exact ⟨Q, by simpa [two_nsmul] using hQQ⟩
  · refine ⟨-Q, ?_⟩
    simp only [two_nsmul]
    calc
      -Q + -Q = -(Q + Q) := by rw [neg_add]
      _ = -(-WeierstrassCurve.Affine.Point.some U V hP) := by
        rw [hQQ]
      _ = WeierstrassCurve.Affine.Point.some U V hP := neg_neg _

/-! ## The four residual squareclasses -/

/-- Every nonzero abscissa on the split model has squareclass `1`, `-3`,
`-7`, or `21`. -/
theorem abscissa_class_of_ne_zero
    {V W : ℚ} (hV0 : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    (∃ r : ℚ, r ≠ 0 ∧ V = r ^ 2) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = -(3 * r ^ 2)) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = -(7 * r ^ 2)) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = 21 * r ^ 2) := by
  have hinv := translate_by_zero_twoTorsion hV0 hcurve
  rcases abscissa_squareClass hV0 hcurve with
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ |
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩
  all_goals
    have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
  · exact Or.inl ⟨r, hr, hc⟩
  · exact (no_negativeOne_squareClass hr hc hcurve).elim
  · exact (no_three_squareClass hr hc hcurve).elim
  · exact Or.inr (Or.inl ⟨r, hr, hc⟩)
  · -- squareclass `7` translates to the impossible class `-1`
    exfalso
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact no_negativeOne_squareClass hr' hc' hinv
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hc⟩))
  · -- squareclass `-21` translates to the impossible class `3`
    exfalso
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = 3 * (1 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact no_three_squareClass hr' hc' hinv

/-! ## The visible torsion points -/

private lemma nonsingular_zero_zero :
    fullTwoCurve.toAffine.Nonsingular 0 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_nine_zero :
    fullTwoCurve.toAffine.Nonsingular 9 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negSeven_zero :
    fullTwoCurve.toAffine.Nonsingular (-7) 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negThree_twelve :
    fullTwoCurve.toAffine.Nonsingular (-3) 12 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negThree_negTwelve :
    fullTwoCurve.toAffine.Nonsingular (-3) (-12) :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_twentyOne_eightyFour :
    fullTwoCurve.toAffine.Nonsingular 21 84 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_twentyOne_negEightyFour :
    fullTwoCurve.toAffine.Nonsingular 21 (-84) :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

/-- The rational two-torsion point `(0,0)`. -/
def T : fullTwoCurve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The rational two-torsion point `(9,0)`. -/
def T₉ : fullTwoCurve.toAffine.Point :=
  .some 9 0 nonsingular_nine_zero

/-- The rational two-torsion point `(-7,0)`. -/
def T₇ : fullTwoCurve.toAffine.Point :=
  .some (-7) 0 nonsingular_negSeven_zero

/-- The visible order-four point `(-3,12)`. -/
def P₃ : fullTwoCurve.toAffine.Point :=
  .some (-3) 12 nonsingular_negThree_twelve

/-- The negative of `P₃`. -/
def P₃neg : fullTwoCurve.toAffine.Point :=
  .some (-3) (-12) nonsingular_negThree_negTwelve

/-- The visible order-four point `(21,84)`. -/
def P₂₁ : fullTwoCurve.toAffine.Point :=
  .some 21 84 nonsingular_twentyOne_eightyFour

/-- The negative of `P₂₁`. -/
def P₂₁neg : fullTwoCurve.toAffine.Point :=
  .some 21 (-84) nonsingular_twentyOne_negEightyFour

private lemma negY_eq {x y : ℚ} :
    fullTwoCurve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_T : -T = T := by
  rw [T, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_P₃ : -P₃ = P₃neg := by
  rw [P₃, P₃neg, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_P₂₁ : -P₂₁ = P₂₁neg := by
  rw [P₂₁, P₂₁neg, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

/-- Adding `(0,0)` to `(-3,12)` gives `(21,84)`. -/
theorem P₃_add_T : P₃ + T = P₂₁ := by
  rw [P₃, T, P₂₁]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (by norm_num : (-3 : ℚ) ≠ 0)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, fullTwoCurve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope, fullTwoCurve]

/-- Adding `(0,0)` to `(21,84)` gives `(-3,12)`. -/
theorem P₂₁_add_T : P₂₁ + T = P₃ := by
  rw [P₃, T, P₂₁]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (by norm_num : (21 : ℚ) ≠ 0)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, fullTwoCurve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope, fullTwoCurve]

/-! ## Coset decompositions for the residual squareclasses -/

private lemma decompose_of_sub_eq_some
    {P R : fullTwoCurve.toAffine.Point} {x y : ℚ}
    {hxy : fullTwoCurve.toAffine.Nonsingular x y}
    (hsub : P - R = .some x y hxy)
    (hx0 : x ≠ 0) (hxSquare : IsSquare x) :
    ∃ Q : fullTwoCurve.toAffine.Point, P = R + (2 : ℕ) • Q := by
  obtain ⟨Q, hQ⟩ :=
    double_of_square_abscissa hx0 hxy hxSquare
  refine ⟨Q, ?_⟩
  calc
    P = R + (P - R) := by abel
    _ = R + (2 : ℕ) • Q := by rw [hsub, hQ]

/-- A point with squareclass `-7` lies in the coset of `T`. -/
private lemma decompose_negSeven_class
    {U V z : ℚ} (hU0 : U ≠ 0)
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hU : U = -(7 * z ^ 2)) :
    ∃ Q : fullTwoCurve.toAffine.Point,
      .some U V hP = T + (2 : ℕ) • Q := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve := fullTwoCurve_equation_of_nonsingular hP
  have hslope :
      fullTwoCurve.toAffine.slope U 0 V 0 = V / U := by
    simp [WeierstrassCurve.Affine.slope, hU0]
  have haddX :
      fullTwoCurve.toAffine.addX U 0
          (fullTwoCurve.toAffine.slope U 0 V 0) = -63 / U := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
    field_simp [hU0]
    nlinarith [hcurve]
  let hsum : fullTwoCurve.toAffine.Nonsingular
      (fullTwoCurve.toAffine.addX U 0
        (fullTwoCurve.toAffine.slope U 0 V 0))
      (fullTwoCurve.toAffine.addY U 0 V
        (fullTwoCurve.toAffine.slope U 0 V 0)) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP nonsingular_zero_zero (fun h ↦ hU0 h.1)
  have hsub :
      (.some U V hP : fullTwoCurve.toAffine.Point) - T =
        .some
          (fullTwoCurve.toAffine.addX U 0
            (fullTwoCurve.toAffine.slope U 0 V 0))
          (fullTwoCurve.toAffine.addY U 0 V
            (fullTwoCurve.toAffine.slope U 0 V 0)) hsum := by
    rw [sub_eq_add_neg, neg_T]
    change (.some U V hP : fullTwoCurve.toAffine.Point) +
        .some 0 0 nonsingular_zero_zero = _
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hU0
  apply decompose_of_sub_eq_some hsub
  · rw [haddX, hU]
    apply div_ne_zero (by norm_num)
    intro h
    rw [h] at hU
    exact hU0 hU
  · refine ⟨3 / z, ?_⟩
    rw [haddX, hU]
    field_simp [hz0]
    ring

/-- The chord identity: subtracting an affine representative multiplies
abscissas into the intercept square.  Stated for the two concrete
order-four representatives via their common shape. -/
private lemma decompose_affine_rep
    {U V xR yR : ℚ}
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hR : fullTwoCurve.toAffine.Nonsingular xR yR)
    (hRneg : fullTwoCurve.toAffine.Nonsingular xR (-yR))
    (hU0 : U ≠ 0) (hxR0 : xR ≠ 0) (hne : U ≠ xR)
    {ρ : ℚ} (hρ0 : ρ ≠ 0) (hprod : U * xR = ρ ^ 2) :
    (∃ Q : fullTwoCurve.toAffine.Point,
      .some U V hP = .some xR yR hR + (2 : ℕ) • Q) ∨
    .some U V hP = .some xR yR hR + T := by
  have hcurveP := fullTwoCurve_equation_of_nonsingular hP
  have hcurveR := fullTwoCurve_equation_of_nonsingular hR
  have hnesub : U - xR ≠ 0 := sub_ne_zero.mpr hne
  have hnegR :
      -(.some xR yR hR : fullTwoCurve.toAffine.Point) =
        .some xR (-yR) hRneg := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨trivial, negY_eq⟩
  set L : ℚ := fullTwoCurve.toAffine.slope U xR V (-yR) with hLdef
  have hL : L * (U - xR) = V + yR := by
    rw [hLdef, WeierstrassCurve.Affine.slope_of_X_ne hne]
    field_simp [hnesub]
    ring
  have haddX :
      fullTwoCurve.toAffine.addX U xR L = L ^ 2 + 2 - U - xR := by
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
  have hkey :
      fullTwoCurve.toAffine.addX U xR L * (U * xR) =
        (V - L * U) ^ 2 := by
    have hA2 : L ^ 2 * (U - xR) ^ 2 = (V + yR) ^ 2 := by
      linear_combination (L * (U - xR) + (V + yR)) * hL
    have hVL2 :
        (V - L * U) ^ 2 * (U - xR) ^ 2 =
          (V * (U - xR) - (V + yR) * U) ^ 2 := by
      linear_combination
        (((V - L * U) * (U - xR) +
            (V * (U - xR) - (V + yR) * U)) * (-U)) * hL
    have hcleared :
        (fullTwoCurve.toAffine.addX U xR L * (U * xR) -
            (V - L * U) ^ 2) * (U - xR) ^ 2 = 0 := by
      rw [haddX]
      linear_combination
        (U * xR) * hA2 - hVL2 + (xR * (U - xR)) * hcurveP -
          (U * (U - xR)) * hcurveR
    have hne2 : (U - xR) ^ 2 ≠ 0 := pow_ne_zero 2 hnesub
    rcases mul_eq_zero.mp hcleared with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne2
  let hsum : fullTwoCurve.toAffine.Nonsingular
      (fullTwoCurve.toAffine.addX U xR L)
      (fullTwoCurve.toAffine.addY U xR V L) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP hRneg (fun h ↦ (hne h.1).elim)
  have hsub :
      (.some U V hP : fullTwoCurve.toAffine.Point) -
          .some xR yR hR =
        .some
          (fullTwoCurve.toAffine.addX U xR L)
          (fullTwoCurve.toAffine.addY U xR V L) hsum := by
    rw [sub_eq_add_neg, hnegR]
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hne
  have hUxR : U * xR ≠ 0 := mul_ne_zero hU0 hxR0
  by_cases hc0 : V - L * U = 0
  · -- the difference is the two-torsion point `(0,0)`
    right
    have haddX0 : fullTwoCurve.toAffine.addX U xR L = 0 := by
      have h0 : fullTwoCurve.toAffine.addX U xR L * (U * xR) = 0 := by
        rw [hkey, hc0]
        norm_num
      exact (mul_eq_zero.mp h0).resolve_right hUxR
    have haddY0 :
        fullTwoCurve.toAffine.addY U xR V L = 0 := by
      have hOn := onFullTwoCurve_of_nonsingular hsum
      rw [haddX0] at hOn
      unfold OnFullTwoCurve at hOn
      norm_num at hOn
      exact hOn
    have hsubT :
        (.some U V hP : fullTwoCurve.toAffine.Point) -
            .some xR yR hR = T := by
      rw [hsub, T]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨haddX0, haddY0⟩
    calc
      (.some U V hP : fullTwoCurve.toAffine.Point) =
          .some xR yR hR +
            ((.some U V hP : fullTwoCurve.toAffine.Point) -
              .some xR yR hR) := by abel
      _ = .some xR yR hR + T := by rw [hsubT]
  · left
    apply decompose_of_sub_eq_some hsub
    · intro h
      rw [h] at hkey
      norm_num at hkey
      exact hc0 ((pow_eq_zero_iff (two_ne_zero)).mp hkey.symm)
    · refine ⟨(V - L * U) / ρ, ?_⟩
      have haddXval : fullTwoCurve.toAffine.addX U xR L =
          (V - L * U) ^ 2 / (U * xR) := by
        rw [eq_div_iff hUxR]
        exact hkey
      rw [haddXval, hprod]
      field_simp [hρ0]

/-! ## The four doubling cosets -/

/-- Every rational point lies in one of four explicit cosets of twice the
rational point group. -/
theorem four_doubling_cosets (P : fullTwoCurve.toAffine.Point) :
    (∃ Q : fullTwoCurve.toAffine.Point, P = (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = T + (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = P₃ + (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = P₂₁ + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hcurve := fullTwoCurve_equation_of_nonsingular hP
      rcases eq_or_ne U 0 with rfl | hU0
      · have hV : V = 0 := by
          norm_num at hcurve
          nlinarith [sq_nonneg V]
        subst V
        right; left
        refine ⟨0, ?_⟩
        simp [T]
      · have hOn : OnFullTwoCurve U V :=
          onFullTwoCurve_of_nonsingular hP
        rcases abscissa_class_of_ne_zero hU0 hOn with
            ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩
        · -- squareclass 1: the point is divisible by two
          left
          obtain ⟨Q, hQ⟩ :=
            double_of_square_abscissa hU0 hP ⟨r, by rw [hU]; ring⟩
          exact ⟨Q, hQ.symm⟩
        · -- squareclass -3: coset of `(-3,12)`
          rcases eq_or_ne U (-3) with rfl | hne
          · have hV : V = 12 ∨ V = -12 := by
              norm_num at hcurve
              have : (V - 12) * (V + 12) = 0 := by nlinarith [hcurve]
              rcases mul_eq_zero.mp this with h | h
              · exact Or.inl (by linarith)
              · exact Or.inr (by linarith)
            rcases hV with rfl | rfl
            · right; right; left
              exact ⟨0, by simp [P₃]⟩
            · right; right; left
              refine ⟨P₃neg, ?_⟩
              rw [← neg_P₃]
              have : (.some (-3) (-12)
                  nonsingular_negThree_negTwelve :
                    fullTwoCurve.toAffine.Point) = -P₃ := by
                rw [neg_P₃]
                rfl
              rw [this]
              simp only [two_nsmul]
              abel
          · have hρ : U * (-3) = (3 * r) ^ 2 := by
              rw [hU]
              ring
            rcases decompose_affine_rep hP
                nonsingular_negThree_twelve
                nonsingular_negThree_negTwelve
                hU0 (by norm_num) hne
                (by positivity : (3 : ℚ) * r ≠ 0) hρ with
                ⟨Q, hQ⟩ | hQ
            · right; right; left
              exact ⟨Q, by rw [hQ]; rfl⟩
            · right; right; right
              refine ⟨0, ?_⟩
              have hPT : (.some (-3) 12
                  nonsingular_negThree_twelve :
                    fullTwoCurve.toAffine.Point) + T = P₂₁ := P₃_add_T
              rw [hQ, hPT]
              simp
        · -- squareclass -7: coset of `T`
          right; left
          exact decompose_negSeven_class hU0 hP hU
        · -- squareclass 21: coset of `(21,84)`
          rcases eq_or_ne U 21 with rfl | hne
          · have hV : V = 84 ∨ V = -84 := by
              norm_num at hcurve
              have : (V - 84) * (V + 84) = 0 := by nlinarith [hcurve]
              rcases mul_eq_zero.mp this with h | h
              · exact Or.inl (by linarith)
              · exact Or.inr (by linarith)
            rcases hV with rfl | rfl
            · right; right; right
              exact ⟨0, by simp [P₂₁]⟩
            · right; right; right
              refine ⟨P₂₁neg, ?_⟩
              rw [← neg_P₂₁]
              have : (.some 21 (-84)
                  nonsingular_twentyOne_negEightyFour :
                    fullTwoCurve.toAffine.Point) = -P₂₁ := by
                rw [neg_P₂₁]
                rfl
              rw [this]
              simp only [two_nsmul]
              abel
          · have hρ : U * 21 = (21 * r) ^ 2 := by
              rw [hU]
              ring
            rcases decompose_affine_rep hP
                nonsingular_twentyOne_eightyFour
                nonsingular_twentyOne_negEightyFour
                hU0 (by norm_num) hne
                (by positivity : (21 : ℚ) * r ≠ 0) hρ with
                ⟨Q, hQ⟩ | hQ
            · right; right; right
              exact ⟨Q, by rw [hQ]; rfl⟩
            · right; right; left
              refine ⟨0, ?_⟩
              have hPT : (.some 21 84
                  nonsingular_twentyOne_eightyFour :
                    fullTwoCurve.toAffine.Point) + T = P₃ := P₂₁_add_T
              rw [hQ, hPT]
              simp

/-! ## Finite index, finite generation, and rank zero -/

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup fullTwoCurve.toAffine.Point :=
  (nsmulAddMonoidHom (α := fullTwoCurve.toAffine.Point) 2).range

private def doublingRepresentative :
    Fin 4 → fullTwoCurve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => P₃
  | 3 => P₂₁

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 4 ↦
        QuotientAddGroup.mk' doublingRange
          (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective doublingRange c
  rcases four_doubling_cosets P with
      ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine
      ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨2, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨3, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm

/-- The image of multiplication by two has finite index. -/
theorem doubling_finiteIndex : doublingRange.FiniteIndex := by
  letI : Finite (fullTwoCurve.toAffine.Point ⧸ doublingRange) :=
    Finite.of_surjective _ doubling_quotient_surjective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The rational point group is finitely generated. -/
theorem point_fg : AddGroup.FG fullTwoCurve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two fullTwoCurve
    doubling_finiteIndex

/-- The multiplication-by-two index is at most four. -/
theorem doubling_index_le_four : doublingRange.index ≤ 4 := by
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      doubling_quotient_surjective).trans_eq (by simp)

/-! ## The rational two-torsion has cardinality four -/

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma double_T₉ : (2 : ℕ) • T₉ = 0 := by
  simp only [two_nsmul]
  rw [T₉]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma double_T₇ : (2 : ℕ) • T₇ = 0 := by
  simp only [two_nsmul]
  rw [T₇]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private def fourToTwoTorsion :
    Fin 4 → {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩
  | 2 => ⟨T₉, double_T₉⟩
  | 3 => ⟨T₇, double_T₇⟩

private lemma fourToTwoTorsion_injective :
    Function.Injective fourToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fourToTwoTorsion, T, T₉, T₇] at hij ⊢
  all_goals norm_num at hij

private lemma fourToTwoTorsion_surjective :
    Function.Surjective fourToTwoTorsion := by
  rintro ⟨P, htwo⟩
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hself :
          WeierstrassCurve.Affine.Point.some U V hP =
            -WeierstrassCurve.Affine.Point.some U V hP := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hV : V = 0 := by
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          true_and] at hself
        norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve] at hself
        linarith
      have hcurve := fullTwoCurve_equation_of_nonsingular hP
      rw [hV] at hcurve
      norm_num at hcurve
      have hU : U = 0 ∨ U = 9 ∨ U = -7 := by
        rcases hcurve with h | h
        · exact Or.inl h
        · have hfac : (U - 9) * (U + 7) = 0 := by
            linear_combination h
          rcases mul_eq_zero.mp hfac with h' | h'
          · exact Or.inr (Or.inl (by linarith))
          · exact Or.inr (Or.inr (by linarith))
      subst hV
      rcases hU with rfl | rfl | rfl
      · exact ⟨1, by apply Subtype.ext; rfl⟩
      · exact ⟨2, by apply Subtype.ext; rfl⟩
      · exact ⟨3, by apply Subtype.ext; rfl⟩

/-- The split model has exactly four rational points killed by two. -/
theorem two_torsion_card_eq_four :
    Nat.card
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  letI : Finite
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion fullTwoCurve
  simpa using
    (Nat.card_congr
      (Equiv.ofBijective fourToTwoTorsion
        ⟨fourToTwoTorsion_injective,
          fourToTwoTorsion_surjective⟩)).symm

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ fullTwoCurve.toAffine.Point = 0 := by
  letI : AddGroup.FG fullTwoCurve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := fullTwoCurve.toAffine.Point) 2).ker = 4 := by
    change Nat.card
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} = 4
    exact two_torsion_card_eq_four
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg fullTwoCurve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow :
      2 ^ Module.finrank ℤ fullTwoCurve.toAffine.Point ≤ 1 := by
    have hindex := doubling_index_le_four
    change
      (nsmulAddMonoidHom
        (α := fullTwoCurve.toAffine.Point) 2).range.index ≤ 4
      at hindex
    omega
  have hpowequal :
      2 ^ Module.finrank ℤ fullTwoCurve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points are torsion; in particular, the rational point
group of the split model is finite. -/
theorem point_finite : Finite fullTwoCurve.toAffine.Point := by
  letI : AddGroup.FG fullTwoCurve.toAffine.Point := point_fg
  letI : Module.Finite ℤ fullTwoCurve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion :
      Module.IsTorsion ℤ fullTwoCurve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion fullTwoCurve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

/-! ## The eight visible points -/

/-- The eight visibly distinct rational points.  No exhaustiveness claim
is made here. -/
def eightVisiblePoints : Fin 8 → fullTwoCurve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => T₉
  | 3 => T₇
  | 4 => P₃
  | 5 => P₃neg
  | 6 => P₂₁
  | 7 => P₂₁neg

theorem eightVisiblePoints_injective :
    Function.Injective eightVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [eightVisiblePoints, T, T₉, T₇, P₃, P₃neg,
      P₂₁, P₂₁neg] at hij ⊢
  all_goals norm_num at hij

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

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩



































/-- The original split-model bound through the public full-torsion interface. -/
theorem point_card_le_eight : Nat.card fullTwoCurve.toAffine.Point ≤ 8 := by
  let W : WeierstrassCurve ℤ := ⟨0, -2, 0, -63, 0⟩
  have hW : W.map (Int.castRingHom ℚ) = fullTwoCurve := by
    ext <;> norm_num [W, fullTwoCurve, WeierstrassCurve.map]
  letI : (W.map (Int.castRingHom ℚ)).IsElliptic := hW.symm ▸ inferInstance
  letI : Finite (W.map (Int.castRingHom ℚ)).toAffine.Point := hW.symm ▸ point_finite
  have hgood : ¬ (5 : ℤ) ∣ W.Δ := by
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hdiv := MazurTransfer.finite_toAffine_card_dvd W 5 (by decide) hgood
  have hcount : Nat.card (W.map (Int.castRingHom (ZMod 5))).toAffine.Point = 8 := by
    exact Nat.card_eq_fintype_card.trans (by decide +kernel)
  have hle := Nat.le_of_dvd (by rw [hcount]; decide) hdiv
  simpa only [hW, hcount] using hle


/-- The eight points constructed by the descent file exhaust the rational
point group. -/
theorem eightVisiblePoints_bijective :
    Function.Bijective eightVisiblePoints := by
  letI : Finite fullTwoCurve.toAffine.Point := point_finite
  exact
    eightVisiblePoints_injective.bijective_of_nat_card_le
      (by simpa using point_card_le_eight)

/-- Every affine rational point of the split model is one of the seven
visible affine points. -/
theorem fullTwo_point_classification
    {U V : ℚ}
    (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    (U = 0 ∧ V = 0) ∨
    (U = 9 ∧ V = 0) ∨
    (U = -7 ∧ V = 0) ∨
    (U = -3 ∧ V = 12) ∨
    (U = -3 ∧ V = -12) ∨
    (U = 21 ∧ V = 84) ∨
    (U = 21 ∧ V = -84) := by
  let P : fullTwoCurve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ :=
    eightVisiblePoints_bijective.2 P
  fin_cases i
  · exfalso
    have hzero : P ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hP
    exact hzero
      (by simpa only [eightVisiblePoints] using hi.symm)
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; left
    have hcoords : (9 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T₉, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; left
    have hcoords : (-7 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T₇, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; left
    have hcoords : (-3 : ℚ) = U ∧ (12 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₃, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; left
    have hcoords : (-3 : ℚ) = U ∧ (-12 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₃neg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; right; left
    have hcoords : (21 : ℚ) = U ∧ (84 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₂₁, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; right; right
    have hcoords : (21 : ℚ) = U ∧ (-84 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₂₁neg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩

/-- Unconditional abscissa classification on the split model. -/
theorem abscissa_eq_of_onFullTwoCurve
    {V W : ℚ} (h : OnFullTwoCurve V W) :
    V = 0 ∨ V = 9 ∨ V = -7 ∨ V = -3 ∨ V = 21 := by
  rcases fullTwo_point_classification
      (nonsingular_of_onFullTwoCurve h) with
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

/-! ## The two quartic leaves become theorems -/

private lemma not_sq_eq_twentyOne_mul_sq
    {m n : ℤ} (hmn : IsCoprime m n)
    (h : m ^ 2 = 21 * n ^ 2) : False := by
  have h3 : (3 : ℤ) ∣ m := by
    have h3sq : (3 : ℤ) ∣ m ^ 2 := ⟨7 * n ^ 2, by linear_combination h⟩
    exact (Int.Prime.dvd_pow' (by norm_num) h3sq)
  obtain ⟨k, hk⟩ := h3
  have h9 : 9 * k ^ 2 = 21 * n ^ 2 := by
    rw [hk] at h
    linear_combination h
  have h3n : (3 : ℤ) ∣ n := by
    have h3sq : (3 : ℤ) ∣ n ^ 2 := by
      have h7 : 3 * k ^ 2 = 7 * n ^ 2 := by linarith
      have hdvd : (3 : ℤ) ∣ 7 * n ^ 2 := ⟨k ^ 2, by linarith⟩
      rcases (Int.Prime.dvd_mul' (by norm_num) hdvd) with h' | h'
      · norm_num at h'
      · exact h'
    exact (Int.Prime.dvd_pow' (by norm_num) h3sq)
  have : IsUnit (3 : ℤ) := hmn.isUnit_of_dvd' ⟨k, hk⟩ h3n
  norm_num [Int.isUnit_iff] at this

private lemma not_three_mul_sq_eq_seven_mul_sq
    {m n : ℤ} (hmn : IsCoprime m n)
    (h : 3 * m ^ 2 = 7 * n ^ 2) : False := by
  have h7 : (7 : ℤ) ∣ m := by
    have h7sq : (7 : ℤ) ∣ m ^ 2 := by
      have hdvd : (7 : ℤ) ∣ 3 * m ^ 2 := ⟨n ^ 2, by linear_combination h⟩
      rcases (Int.Prime.dvd_mul' (by norm_num) hdvd) with h' | h'
      · norm_num at h'
      · exact h'
    exact (Int.Prime.dvd_pow' (by norm_num) h7sq)
  obtain ⟨k, hk⟩ := h7
  have h49 : 3 * (49 * k ^ 2) = 7 * n ^ 2 := by
    rw [hk] at h
    linear_combination h
  have h7n : (7 : ℤ) ∣ n := by
    have h7sq : (7 : ℤ) ∣ n ^ 2 := by
      have h21 : 21 * k ^ 2 = n ^ 2 := by linarith
      exact ⟨3 * k ^ 2, by linarith⟩
    exact (Int.Prime.dvd_pow' (by norm_num) h7sq)
  have : IsUnit (7 : ℤ) := hmn.isUnit_of_dvd' ⟨k, hk⟩ h7n
  norm_num [Int.isUnit_iff] at this

/-- The principal quartic leaf, now a theorem. -/
theorem principalQuarticClassified : PrincipalQuarticClassified := by
  intro m n c hmn hc
  by_cases hm : m = 0
  · exact Or.inl hm
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  right; right
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  set V : ℚ := ((m : ℚ) / n) ^ 2 with hVdef
  set W : ℚ := (m : ℚ) * c / n ^ 3 with hWdef
  have hOn : OnFullTwoCurve V W := by
    unfold OnFullTwoCurve
    rw [hVdef, hWdef]
    have hcQ : (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hc
    field_simp
    linear_combination hcQ
  have hVpos : 0 < V := by
    rw [hVdef]
    positivity
  rcases abscissa_eq_of_onFullTwoCurve hOn with
      h | h | h | h | h
  · exact absurd h (by positivity)
  · -- `V = 9` forces `m² = 9n²`
    rw [hVdef] at h
    have : (m : ℚ) ^ 2 = 9 * n ^ 2 := by
      field_simp at h
      linear_combination h
    exact_mod_cast this
  · exact absurd h (by intro h'; rw [h'] at hVpos; norm_num at hVpos)
  · exact absurd h (by intro h'; rw [h'] at hVpos; norm_num at hVpos)
  · -- `V = 21` contradicts primitivity
    exfalso
    rw [hVdef] at h
    have h21 : (m : ℚ) ^ 2 = 21 * n ^ 2 := by
      field_simp at h
      linear_combination h
    exact not_sq_eq_twentyOne_mul_sq hmn (by exact_mod_cast h21)

/-- The second quartic leaf, now a theorem. -/
theorem negativeThreeQuarticClassified :
    NegativeThreeQuarticClassified := by
  intro m n c hmn hc
  by_cases hm : m = 0
  · exact Or.inl hm
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  right; right
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  set V : ℚ := -(3 * ((m : ℚ) / n) ^ 2) with hVdef
  set W : ℚ := 3 * (m : ℚ) * c / n ^ 3 with hWdef
  have hOn : OnFullTwoCurve V W := by
    unfold OnFullTwoCurve
    rw [hVdef, hWdef]
    have hcQ : (c : ℚ) ^ 2 =
        -3 * (m : ℚ) ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hc
    field_simp
    linear_combination 3 * hcQ
  have hVneg : V < 0 := by
    rw [hVdef]
    have : 0 < 3 * ((m : ℚ) / n) ^ 2 := by positivity
    linarith
  rcases abscissa_eq_of_onFullTwoCurve hOn with
      h | h | h | h | h
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)
  · -- `V = -7` contradicts primitivity
    exfalso
    rw [hVdef] at h
    have h37 : 3 * (m : ℚ) ^ 2 = 7 * n ^ 2 := by
      field_simp at h
      linear_combination -h
    exact not_three_mul_sq_eq_seven_mul_sq hmn (by exact_mod_cast h37)
  · -- `V = -3` forces `m² = n²`
    rw [hVdef] at h
    have : (m : ℚ) ^ 2 = n ^ 2 := by
      field_simp at h
      linear_combination -h
    exact_mod_cast this
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)

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
  fullTwo_affine_classification
    principalQuarticClassified negativeThreeQuarticClassified hcurve

end MazurTorsion.XZeroTwentyOne

end

theorem solution (V W : ℚ) (hcurve : W ^ 2 = V * (V - 9) * (V + 7)) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) :=
  MazurTorsion.XZeroTwentyOne.fullTwo_affine_classification_unconditional hcurve
#print axioms solution
