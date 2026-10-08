-- Prove2me | solution 1 for MazurTransfer.order_twenty_seven_legs_chain_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:09:51.192921+00:00
-- url     : https://prove2.me/submissions/fbdd676b-0dc6-4989-8dbe-d116b005c27d

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_XZeroTwentySevenMapCertificateData

import Theorems.Thm_MazurTransfer_x0_27_map_certificate_1
import Theorems.Thm_MazurTransfer_x0_27_map_certificate_2


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegs. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The first two hauptmodul legs of the order-twenty-seven tower

On the parametrized `X₁(9)` family the marked subgroup chain produces
`t₃`-hauptmodul values for the curve and its Vélu quotient:

`a₁leg = (f²-f+1)³(f³-6f²+3f+1)/(f³(f-1)³)`,
`a₂leg = (f³-6f²+3f+1)³/(f(f-1)(f²-f+1)³)`.

Both satisfy cleared `j`-identities against their curves, and the pair
satisfies the Fricke-twisted `X₀(9)` fibre relation `G9F`.  Every
identity in this file is a literal polynomial identity, verified by
`ring` after clearing.
-/

namespace MazurTorsion.Kubert





















/-- The two legs satisfy the cleared Fricke-twisted `X₀(9)` relation. -/
theorem legs_G9F_relation (f : ℚ) :
    a1legN f ^ 2 * a1legD f * a2legN f ^ 3 +
        36 * a1legN f ^ 2 * a1legD f * a2legN f ^ 2 * a2legD f +
        270 * a1legN f ^ 2 * a1legD f * a2legN f * a2legD f ^ 2 -
        a1legN f ^ 3 * a2legD f ^ 3 +
        729 * a1legN f * a1legD f ^ 2 * a2legN f ^ 2 * a2legD f +
        26244 * a1legN f * a1legD f ^ 2 * a2legN f * a2legD f ^ 2 +
        531441 * a1legD f ^ 3 * a2legN f * a2legD f ^ 2 = 0 := by
  simp only [a1legN, a1legD, a2legN, a2legD]
  ring

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.NumberTheory.FermatCubicClassification. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rational points of the Fermat cubic

The affine Fermat cubic `u³ + v³ = 1` has exactly the two rational
points `(1,0)` and `(0,1)`.  This is Euler's case of Fermat's last
theorem, available in mathlib as `fermatLastTheoremThree`; it is the
Diophantine core of the modular curve `X₀(27)`, which the order-27
exclusion reduces to.
-/

namespace MazurTorsion

/-- The affine Fermat cubic has only its two trivial rational points. -/
theorem fermat_cubic_rational_points (u v : ℚ)
    (h : u ^ 3 + v ^ 3 = 1) :
    (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1) := by
  have hflt : FermatLastTheoremWith ℚ 3 :=
    ((fermatLastTheoremWith_nat_int_rat_tfae 3).out 0 2).mp
      fermatLastTheoremThree
  by_cases hu : u = 0
  · subst hu
    right
    refine ⟨rfl, ?_⟩
    have hv : v ^ 3 = 1 := by linarith
    have hfac : (v - 1) * (v ^ 2 + v + 1) = 0 := by
      linear_combination hv
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · exfalso
      nlinarith [sq_nonneg (2 * v + 1)]
  by_cases hv : v = 0
  · subst hv
    left
    refine ⟨?_, rfl⟩
    have hu3 : u ^ 3 = 1 := by linarith
    have hfac : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      linear_combination hu3
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · exfalso
      nlinarith [sq_nonneg (2 * u + 1)]
  · exfalso
    exact hflt u v 1 hu hv one_ne_zero (by rw [h]; norm_num)

/-- The affine rational points of the minimal `X₀(27)` model
`y² + y = x³ - 7` are exactly `(3, 4)` and `(3, -5)`. -/
theorem x0_twentySeven_affine_points (x y : ℚ)
    (h : y ^ 2 + y = x ^ 3 - 7) :
    (x = 3 ∧ y = 4) ∨ (x = 3 ∧ y = -5) := by
  set X : ℚ := 4 * x with hX
  set Y : ℚ := 8 * y + 4 with hY
  have hW : Y ^ 2 = X ^ 3 - 432 := by
    rw [hX, hY]
    linear_combination 64 * h
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0] at hW
    nlinarith [sq_nonneg Y]
  have hu : ((36 + Y) / (6 * X)) ^ 3 + ((36 - Y) / (6 * X)) ^ 3 = 1 := by
    field_simp
    linear_combination 216 * hW
  have h6X : (6 : ℚ) * X ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp hz with hz | hz
    · norm_num at hz
    · exact hX0 hz
  rcases fermat_cubic_rational_points _ _ hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `u = 1, v = 0`: the point `(3, 4)`
    left
    have hYv : 36 - Y = 0 := by
      rcases div_eq_zero_iff.mp h2 with h' | h'
      · exact h'
      · exact absurd h' h6X
    have hXv : 36 + Y = 6 * X := by
      field_simp at h1
      linarith [h1]
    constructor
    · rw [hX] at hXv
      linarith
    · rw [hY] at hYv
      linarith
  · -- `u = 0, v = 1`: the point `(3, -5)`
    right
    have hYv : 36 + Y = 0 := by
      rcases div_eq_zero_iff.mp h1 with h' | h'
      · exact h'
      · exact absurd h' h6X
    have hXv : 36 - Y = 6 * X := by
      field_simp at h2
      linarith [h2]
    constructor
    · rw [hX] at hXv
      linarith
    · rw [hY] at hYv
      linarith

end MazurTorsion

end


/- Source module: MazurTorsion.NumberTheory.XZeroTwentySevenClassification. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rational points of the chained `X₀(9)` correspondence

The order-twenty-seven tower produces three hauptmodul legs
`(s₁, s₂, s₃)` whose consecutive pairs satisfy the Fricke-twisted
`X₀(9)` relation `orderNineG9F`.  The resulting space curve is a model
of `X₀(27)`: an explicit rational map, verified here by two polynomial
certificates, sends every point with nonvanishing denominators to an
affine rational point of `y² + y = x³ - 7`, which the Fermat cubic
classifies.  Four Bezout eliminant certificates handle the vanishing
denominators, and three monic integral polynomials with no root modulo
seven absorb every irrational branch.  The only rational points of the
chain are the cusp `(0, 0, 0)` and the CM point `(-243, -27, -3)`.
-/

namespace MazurTorsion.XZeroTwentySeven

open Kubert (orderNineG9F)

/-! ### Rational-root exclusions -/

private noncomputable def levelNineQuadratic : Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.C 486 * Polynomial.X - Polynomial.C 19683

private lemma levelNineQuadratic_monic :
    Polynomial.Monic levelNineQuadratic := by
  unfold levelNineQuadratic
  monicity!

private lemma levelNineQuadratic_no_root_mod_seven :
    ∀ z : ZMod 7, z ^ 2 - 486 * z - 19683 ≠ 0 := by
  decide

/-- The eliminant factor `t² - 486t - 19683` has irrational roots. -/
private theorem levelNineQuadratic_ne_zero (t : ℚ) :
    t ^ 2 - 486 * t - 19683 ≠ 0 := by
  intro ht
  have hroot : Polynomial.aeval t levelNineQuadratic = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [levelNineQuadratic]
    linear_combination ht
  obtain ⟨z, htz, -⟩ :=
    exists_integer_of_is_root_of_monic levelNineQuadratic_monic hroot
  have hzrat : (z : ℚ) ^ 2 - 486 * (z : ℚ) - 19683 = 0 := by
    have hzcast : (z : ℚ) = t := by
      simpa using htz.symm
    rw [hzcast]
    linear_combination ht
  have hzint : z ^ 2 - 486 * z - 19683 = 0 := by
    exact_mod_cast hzrat
  apply levelNineQuadratic_no_root_mod_seven (z : ZMod 7)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 7)) hzint

private noncomputable def levelNineCubicA : Polynomial ℤ :=
  Polynomial.X ^ 3 - Polynomial.C 207 * Polynomial.X ^ 2 +
    Polynomial.C 50571 * Polynomial.X + Polynomial.C 3

private lemma levelNineCubicA_monic :
    Polynomial.Monic levelNineCubicA := by
  unfold levelNineCubicA
  monicity!

private lemma levelNineCubicA_no_root_mod_seven :
    ∀ z : ZMod 7, z ^ 3 - 207 * z ^ 2 + 50571 * z + 3 ≠ 0 := by
  decide

/-- The fiber cubic over `s₂ = -3` has no rational root. -/
private theorem levelNineCubicA_ne_zero (t : ℚ) :
    t ^ 3 - 207 * t ^ 2 + 50571 * t + 3 ≠ 0 := by
  intro ht
  have hroot : Polynomial.aeval t levelNineCubicA = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [levelNineCubicA]
    linear_combination ht
  obtain ⟨z, htz, -⟩ :=
    exists_integer_of_is_root_of_monic levelNineCubicA_monic hroot
  have hzrat : (z : ℚ) ^ 3 - 207 * (z : ℚ) ^ 2 + 50571 * (z : ℚ) + 3 = 0 := by
    have hzcast : (z : ℚ) = t := by
      simpa using htz.symm
    rw [hzcast]
    linear_combination ht
  have hzint : z ^ 3 - 207 * z ^ 2 + 50571 * z + 3 = 0 := by
    exact_mod_cast hzrat
  apply levelNineCubicA_no_root_mod_seven (z : ZMod 7)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 7)) hzint

private noncomputable def levelNineCubicB : Polynomial ℤ :=
  Polynomial.X ^ 3 + Polynomial.C 12288753 * Polynomial.X ^ 2 -
    Polynomial.C 36669429 * Polynomial.X + Polynomial.C 129140163

private lemma levelNineCubicB_monic :
    Polynomial.Monic levelNineCubicB := by
  unfold levelNineCubicB
  monicity!

private lemma levelNineCubicB_no_root_mod_seven :
    ∀ z : ZMod 7, z ^ 3 + 12288753 * z ^ 2 - 36669429 * z + 129140163 ≠ 0 := by
  decide

/-- The fiber cubic over `s₂ = -243` has no rational root. -/
private theorem levelNineCubicB_ne_zero (t : ℚ) :
    t ^ 3 + 12288753 * t ^ 2 - 36669429 * t + 129140163 ≠ 0 := by
  intro ht
  have hroot : Polynomial.aeval t levelNineCubicB = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [levelNineCubicB]
    linear_combination ht
  obtain ⟨z, htz, -⟩ :=
    exists_integer_of_is_root_of_monic levelNineCubicB_monic hroot
  have hzrat : (z : ℚ) ^ 3 + 12288753 * (z : ℚ) ^ 2 - 36669429 * (z : ℚ) + 129140163 = 0 := by
    have hzcast : (z : ℚ) = t := by
      simpa using htz.symm
    rw [hzcast]
    linear_combination ht
  have hzint : z ^ 3 + 12288753 * z ^ 2 - 36669429 * z + 129140163 = 0 := by
    exact_mod_cast hzrat
  apply levelNineCubicB_no_root_mod_seven (z : ZMod 7)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 7)) hzint

/-! ### The transfer map to `X₀(27)` -/









/-! The intermediate remainder of the two-step division of the cleared
curve identity by the two correspondence polynomials, in chunks. -/



















































/-! The two division cofactors, in chunks. -/













































































private lemma curve_key_step₁ {s₁ s₂ s₃ : ℚ}
    (h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0) :
    (mapNya s₂ s₃ ^ 2 + mapNya s₂ s₃ * mapDya s₂ s₃ + 7 * mapDya s₂ s₃ ^ 2) *
        mapDx s₁ s₂ s₃ ^ 3 - mapNx s₁ s₂ s₃ ^ 3 * mapDya s₂ s₃ ^ 2 =
      remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
        + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
        + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
        + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
        + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
        + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃
        + remPart24 s₂ s₃ := by
  exact MazurTransfer.x0_27_map_certificate_1 h1


private lemma curve_key_step₂ {s₁ s₂ s₃ : ℚ}
    (h2 : s₂ ^ 2 * s₃ ^ 3 + 36 * s₂ ^ 2 * s₃ ^ 2 + 270 * s₂ ^ 2 * s₃ - s₂ ^ 3 +
      729 * s₂ * s₃ ^ 2 + 26244 * s₂ * s₃ + 531441 * s₃ = 0) :
    remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
      + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
      + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
      + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
      + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
      + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃ + remPart24 s₂ s₃
      = 0 := by
  exact MazurTransfer.x0_27_map_certificate_2 h2


/-- On the space curve the transfer map lands on `y² + y = x³ - 7`. -/
private lemma transfer_on_curve {s₁ s₂ s₃ : ℚ}
    (h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0)
    (h2 : s₂ ^ 2 * s₃ ^ 3 + 36 * s₂ ^ 2 * s₃ ^ 2 + 270 * s₂ ^ 2 * s₃ - s₂ ^ 3 +
      729 * s₂ * s₃ ^ 2 + 26244 * s₂ * s₃ + 531441 * s₃ = 0)
    (hDya : mapDya s₂ s₃ ≠ 0) (hDx : mapDx s₁ s₂ s₃ ≠ 0) :
    (mapNya s₂ s₃ / mapDya s₂ s₃) ^ 2 + mapNya s₂ s₃ / mapDya s₂ s₃ =
      (mapNx s₁ s₂ s₃ / mapDx s₁ s₂ s₃) ^ 3 - 7 := by
  have key := (curve_key_step₁ h1).trans (curve_key_step₂ h2)
  field_simp
  linear_combination key

/-! ### The classification -/

/-- The only rational points of the chained Fricke-twisted `X₀(9)`
correspondence are the cusp chain `(0, 0, 0)` and the CM chain
`(-243, -27, -3)`. -/
theorem spaceCurve_classification {s₁ s₂ s₃ : ℚ}
    (hG1 : orderNineG9F s₁ s₂ = 0) (hG2 : orderNineG9F s₂ s₃ = 0) :
    s₁ = 0 ∧ s₂ = 0 ∧ s₃ = 0 ∨ s₁ = -243 ∧ s₂ = -27 ∧ s₃ = -3 := by
  have h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0 := by
    simpa only [orderNineG9F] using hG1
  have h2 : s₂ ^ 2 * s₃ ^ 3 + 36 * s₂ ^ 2 * s₃ ^ 2 + 270 * s₂ ^ 2 * s₃ - s₂ ^ 3 +
      729 * s₂ * s₃ ^ 2 + 26244 * s₂ * s₃ + 531441 * s₃ = 0 := by
    simpa only [orderNineG9F] using hG2
  by_cases hs20 : s₂ = 0
  · subst hs20
    refine Or.inl ⟨?_, rfl, ?_⟩
    · have h3 : s₁ ^ 3 = 0 := by linear_combination -h1
      exact pow_eq_zero_iff (by norm_num) |>.mp h3
    · linear_combination h2 / 531441
  · have hs2243 : s₂ + 243 ≠ 0 := by
      intro hz
      have hs2v : s₂ = -243 := by linarith
      subst hs2v
      exact levelNineCubicB_ne_zero s₁ (by linear_combination -h1)
    have hQ2 := levelNineQuadratic_ne_zero s₂
    have hDya : s₂ * s₃ ^ 2 + 18 * s₂ * s₃ + 27 * s₂ + 1458 * s₃ ≠ 0 := by
      intro hz
      have hra : s₂ * ((s₂ + 243) ^ 2 *
          (s₂ ^ 2 - 486 * s₂ - 19683) ^ 2) = 0 := by
        linear_combination
          ( s₂ ^ 5 * s₃ + 18 * s₂ ^ 5 - 81 * s₂ ^ 4 * s₃ ^ 2 - 2430 * s₂ ^ 4 * s₃ - 11664 * s₂ ^ 4
            + 13122 * s₂ ^ 3 * s₃ ^ 2 + 393660 * s₂ ^ 3 * s₃ + 354294 * s₂ ^ 3
            + 1594323 * s₂ ^ 2 * s₃ ^ 2 + 66961566 * s₂ ^ 2 * s₃ + 703096443 * s₂ ^ 2
            + 1162261467 * s₂ * s₃ + 48814981614 * s₂ + 847288609443) * hz +
            ( -s₂ ^ 4 + 81 * s₂ ^ 3 * s₃ + 972 * s₂ ^ 3 - 13122 * s₂ ^ 2 * s₃ - 98415 * s₂ ^ 2
              - 1594323 * s₂ * s₃ - 47829690 * s₂ - 2324522934) * h2
      rcases mul_eq_zero.mp hra with h | h
      · exact hs20 h
      rcases mul_eq_zero.mp h with h | h
      · exact hs2243 (pow_eq_zero_iff (by norm_num) |>.mp h)
      · exact hQ2 (pow_eq_zero_iff (by norm_num) |>.mp h)
    by_cases hA : s₁ + 243 = 0
    · -- `s₁ = -243`: the fiber factors through `E3`
      have hs1v : s₁ = -243 := by linarith
      subst hs1v
      have hE3 : (s₂ + 3) ^ 2 * (s₂ + 27) = 0 := by
        linear_combination h1 / 59049
      rcases mul_eq_zero.mp hE3 with h | h
      · exfalso
        have hs2v : s₂ = -3 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
          linarith
        subst hs2v
        exact levelNineCubicA_ne_zero s₃ (by linear_combination h2 / 9)
      · have hs2v : s₂ = -27 := by linarith
        subst hs2v
        have hE4 : (s₃ + 3) ^ 3 = 0 := by
          linear_combination h2 / 729
        have hs3v : s₃ = -3 := by
          have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hE4
          linarith
        exact Or.inr ⟨rfl, rfl, hs3v⟩
    · by_cases hL : s₁ * s₂ + 18 * s₁ + 729 = 0
      · exfalso
        have hRL : (s₁ ^ 2 - 486 * s₁ - 19683) ^ 2 = 0 := by
          linear_combination
            ( s₁ ^ 2 * s₂ ^ 2 + 18 * s₁ ^ 2 * s₂ - 54 * s₁ ^ 2 + 13122 * s₁ + 531441
              ) * hL - s₁ * h1
        exact levelNineQuadratic_ne_zero s₁
          (pow_eq_zero_iff (by norm_num) |>.mp hRL)
      · -- both denominators are nonzero: transfer to `X₀(27)`
        have hDya' : mapDya s₂ s₃ ≠ 0 := by
          simp only [mapDya]
          exact hDya
        have hDx' : mapDx s₁ s₂ s₃ ≠ 0 := by
          simp only [mapDx]
          exact mul_ne_zero (mul_ne_zero hA hL) hDya'
        have hcurve := transfer_on_curve h1 h2 hDya' hDx'
        rcases x0_twentySeven_affine_points _ _ hcurve with ⟨-, hy⟩ | ⟨-, hy⟩
        · -- ordinate `4`: certificate `p` forces `s₂ = -27`, then `E6`
          exfalso
          rw [div_eq_iff hDya'] at hy
          simp only [mapNya, mapDya] at hy
          have hrp : (s₂ + 27) * ((s₂ + 243) ^ 2 *
              (s₂ ^ 2 - 486 * s₂ - 19683) ^ 2) = 0 := by
            linear_combination
              ( -s₂ ^ 5 * s₃ - 15 * s₂ ^ 5 + 99 * s₂ ^ 4 * s₃ ^ 2 + 2754 * s₂ ^ 4 * s₃
                + 9234 * s₂ ^ 4 - 13122 * s₂ ^ 3 * s₃ ^ 2 - 433026 * s₂ ^ 3 * s₃ - 944784 * s₂ ^ 3
                - 531441 * s₂ ^ 2 * s₃ ^ 2 - 28697814 * s₂ ^ 2 * s₃ - 377854551 * s₂ ^ 2
                - 387420489 * s₂ * s₃ - 19758444939 * s₂ - 282429536481) * hy / 9 +
                ( -9 * s₂ ^ 4 + 891 * s₂ ^ 3 * s₃ + 11421 * s₂ ^ 3 - 118098 * s₂ ^ 2 * s₃
                  - 2125764 * s₂ ^ 2 - 4782969 * s₂ * s₃ - 186535791 * s₂ - 3486784401) * h2 / 9
          have hs2v : s₂ = -27 := by
            rcases mul_eq_zero.mp hrp with h | h
            · linarith
            rcases mul_eq_zero.mp h with h | h
            · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
                hs2243
            · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
                hQ2
          subst hs2v
          have hE6 : (s₁ + 243) ^ 3 = 0 := by
            linear_combination -h1
          exact hA (pow_eq_zero_iff (by norm_num) |>.mp hE6)
        · -- ordinate `-5`: certificate `m` has no surviving factor
          exfalso
          rw [div_eq_iff hDya'] at hy
          simp only [mapNya, mapDya] at hy
          have hrm : (s₂ + 243) ^ 2 *
              (s₂ ^ 2 - 486 * s₂ - 19683) ^ 2 = 0 := by
            linear_combination
              ( -s₂ ^ 4 * s₃ ^ 2 - 27 * s₂ ^ 4 * s₃ - 27 * s₂ ^ 4 + 486 * s₂ ^ 3 * s₃ ^ 2
                + 15309 * s₂ ^ 3 * s₃ + 45927 * s₂ ^ 3 - 59049 * s₂ ^ 2 * s₃ ^ 2
                - 1948617 * s₂ ^ 2 * s₃ - 11691702 * s₂ ^ 2 - 43046721 * s₂ * s₃ - 1420541793 * s₂
                - 31381059609) * hy / 27 +
                ( -27 * s₂ ^ 3 + 19683 * s₂ ^ 2 - 4782969 * s₂ + 387420489) * h2 / 27
          rcases mul_eq_zero.mp hrm with h | h
          · exact hs2243 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
          · exact hQ2 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

end MazurTorsion.XZeroTwentySeven

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenEndpoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The endgame of the order-twenty-seven tower

On the parametrized `X₁(9)` family the first two hauptmodul legs are
never cuspidal, and the first leg never takes the CM value `-243`: the
would-be CM parameter satisfies a monic integral polynomial of degree
nine with no root modulo two.  Combined with the classification of the
chained `X₀(9)` correspondence, any third leg completing the chain is
impossible.  Producing such a third leg from a rational point of exact
order twenty-seven is the remaining step of the exclusion.
-/

namespace MazurTorsion.Kubert

private lemma quadratic_pos (f : ℚ) : 0 < f ^ 2 - f + 1 := by
  nlinarith [sq_nonneg (2 * f - 1)]

private noncomputable def cmLegPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 9 - Polynomial.C 9 * Polynomial.X ^ 8 +
    Polynomial.C 27 * Polynomial.X ^ 7 + Polynomial.C 192 * Polynomial.X ^ 6 -
    Polynomial.C 666 * Polynomial.X ^ 5 + Polynomial.C 675 * Polynomial.X ^ 4 -
    Polynomial.C 213 * Polynomial.X ^ 3 - Polynomial.C 9 * Polynomial.X ^ 2 +
    Polynomial.C 1

private lemma cmLegPolynomial_monic :
    Polynomial.Monic cmLegPolynomial := by
  unfold cmLegPolynomial
  monicity!

private lemma cmLegPolynomial_no_root_mod_two :
    ∀ z : ZMod 2, z ^ 9 - 9 * z ^ 8 + 27 * z ^ 7 + 192 * z ^ 6 - 666 * z ^ 5 +
      675 * z ^ 4 - 213 * z ^ 3 - 9 * z ^ 2 + 1 ≠ 0 := by
  decide

/-- The first hauptmodul leg never takes the CM value `-243`. -/
private theorem firstLeg_ne_cm (f : ℚ) : a1legN f + 243 * a1legD f ≠ 0 := by
  intro h
  have hP : f ^ 9 - 9 * f ^ 8 + 27 * f ^ 7 + 192 * f ^ 6 - 666 * f ^ 5 +
      675 * f ^ 4 - 213 * f ^ 3 - 9 * f ^ 2 + 1 = 0 := by
    simp only [a1legN, a1legD] at h
    linear_combination h
  have hroot : Polynomial.aeval f cmLegPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [cmLegPolynomial]
    linear_combination hP
  obtain ⟨z, hfz, -⟩ :=
    exists_integer_of_is_root_of_monic cmLegPolynomial_monic hroot
  have hzrat : (z : ℚ) ^ 9 - 9 * (z : ℚ) ^ 8 + 27 * (z : ℚ) ^ 7 +
      192 * (z : ℚ) ^ 6 - 666 * (z : ℚ) ^ 5 + 675 * (z : ℚ) ^ 4 -
      213 * (z : ℚ) ^ 3 - 9 * (z : ℚ) ^ 2 + 1 = 0 := by
    have hzcast : (z : ℚ) = f := by
      simpa using hfz.symm
    rw [hzcast]
    linear_combination hP
  have hzint : z ^ 9 - 9 * z ^ 8 + 27 * z ^ 7 + 192 * z ^ 6 - 666 * z ^ 5 +
      675 * z ^ 4 - 213 * z ^ 3 - 9 * z ^ 2 + 1 = 0 := by
    exact_mod_cast hzrat
  apply cmLegPolynomial_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

/-- No rational value can complete the two family legs to a chain of
the Fricke-twisted `X₀(9)` correspondence. -/
theorem legs_chain_impossible (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s₃ : ℚ)
    (h2 : orderNineG9F (a2legN f / a2legD f) s₃ = 0) : False := by
  have hquad : f ^ 2 - f + 1 ≠ 0 := (quadratic_pos f).ne'
  have hD1 : a1legD f ≠ 0 := by
    simp only [a1legD]
    exact mul_ne_zero (pow_ne_zero 3 hf0)
      (pow_ne_zero 3 (sub_ne_zero.mpr hf1))
  have hD2 : a2legD f ≠ 0 := by
    simp only [a2legD]
    exact mul_ne_zero (mul_ne_zero hf0 (sub_ne_zero.mpr hf1))
      (pow_ne_zero 3 hquad)
  have hG1 : orderNineG9F (a1legN f / a1legD f) (a2legN f / a2legD f) = 0 := by
    simp only [orderNineG9F]
    field_simp
    linear_combination legs_G9F_relation f
  rcases XZeroTwentySeven.spaceCurve_classification hG1 h2 with
    ⟨hs1, -, -⟩ | ⟨hs1, -, -⟩
  · rcases div_eq_zero_iff.mp hs1 with h | h
    · simp only [a1legN] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hquad (pow_eq_zero_iff (by norm_num) |>.mp h')
      · exact hK h'
    · exact hD1 h
  · have hcm : a1legN f + 243 * a1legD f = 0 := by
      rw [div_eq_iff hD1] at hs1
      linear_combination hs1
    exact firstLeg_ne_cm f hcm

end MazurTorsion.Kubert

end

namespace MazurTransfer

/-- The order-27 tower cannot have a third rational leg. -/
theorem order_twenty_seven_legs_chain_impossible
    (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s3 : ℚ)
    (h2 : MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s3 = 0) : False := by
  exact MazurTorsion.Kubert.legs_chain_impossible f hf0 hf1 hK s3 h2

end MazurTransfer

#print axioms MazurTransfer.order_twenty_seven_legs_chain_impossible


theorem solution
    (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s3 : ℚ)
    (h2 : MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s3 = 0) : False  := by
  exact MazurTransfer.order_twenty_seven_legs_chain_impossible f hf0 hf1 hK s3 h2

#print axioms solution
