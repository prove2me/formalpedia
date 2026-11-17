-- Prove2me | solution 1 for N25.unitAnalytic25_eq_normalized_ratio
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:10.127204+00:00
-- url     : https://prove2.me/submissions/805854dd-d6be-466c-b6d7-1c1741cde018

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitResidues25_bernoulli_diff
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_etaAnalytic25_ne_zero

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25

/-- The exact Bernoulli difference leaves the frozen integral q-order after normalizing the four eta factors. -/
theorem _root_.solution (i : Fin 5) (τ : UpperHalfPlane) :
    let R : ℕ → ℂ := fun g => etaAnalytic25 g τ /
      Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))
    unitAnalytic25 i τ =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ unitQOrder25 i *
      ((R (unitResidues25 i).1 * R (unitResidues25 i).2) /
        (R (unitResidues25 (i + 1)).1 * R (unitResidues25 (i + 1)).2)) := by
  dsimp only
  let E : ℕ → ℂ := fun g => Complex.exp (Real.pi * Complex.I *
    (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))
  have hc : (25 / 2 : ℂ) *
      ((((unitResidues25 i).1 : ℂ) / 25) ^ 2 - ((unitResidues25 i).1 : ℂ) / 25 + 1 / 6 +
       (((unitResidues25 i).2 : ℂ) / 25) ^ 2 - ((unitResidues25 i).2 : ℂ) / 25 + 1 / 6 -
       ((((unitResidues25 (i + 1)).1 : ℂ) / 25) ^ 2 - ((unitResidues25 (i + 1)).1 : ℂ) / 25 + 1 / 6 +
        (((unitResidues25 (i + 1)).2 : ℂ) / 25) ^ 2 - ((unitResidues25 (i + 1)).2 : ℂ) / 25 + 1 / 6)) =
      (unitQOrder25 i : ℂ) := by
    have h := congrArg (fun x : ℚ => (x : ℂ)) (unitResidues25_bernoulli_diff i)
    push_cast at h
    exact h
  have hphase : E (unitResidues25 i).1 * E (unitResidues25 i).2 /
      (E (unitResidues25 (i + 1)).1 * E (unitResidues25 (i + 1)).2) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ unitQOrder25 i := by
    dsimp only [E]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    linear_combination (2 * Real.pi * Complex.I * (τ : ℂ)) * hc
  have hb (j : Fin 5) : 0 < (unitResidues25 j).1 ∧ (unitResidues25 j).1 < 25 ∧
      0 < (unitResidues25 j).2 ∧ (unitResidues25 j).2 < 25 := by
    fin_cases j <;> decide
  have hn (j : Fin 5) : etaAnalytic25 (unitResidues25 j).1 τ ≠ 0 ∧
      etaAnalytic25 (unitResidues25 j).2 τ ≠ 0 :=
    ⟨etaAnalytic25_ne_zero _ (hb j).1 (hb j).2.1 τ,
      etaAnalytic25_ne_zero _ (hb j).2.2.1 (hb j).2.2.2 τ⟩
  rw [← hphase]
  dsimp only [unitAnalytic25, E]
  field_simp [Complex.exp_ne_zero, (hn i).1, (hn i).2,
    (hn (i + 1)).1, (hn (i + 1)).2]
  <;> ring

end N25
