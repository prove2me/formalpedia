-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_pole_le_weighted_at_place
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:33:46.886128+00:00
-- url     : https://prove2.me/submissions/af3fc34d-5772-4528-977a-1deb880f4f18

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (x : Fin d → E) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) :
    ∀ nu : PolynomialCurvePlace E,
      0 ≤ max (-(polynomialCurveOrder nu (x k) : Real)) 0 ∧
        max (-(polynomialCurveOrder nu (x k) : Real)) 0 ≤
          (w k : Real) * polynomialCurvePole nu x w := by
  classical
  intro nu
  refine ⟨le_max_right _ _, ?_⟩
  let entry : Option (Fin d) → Real :=
    fun i => i.elim 0 (fun j => -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))
  have hpole : polynomialCurvePole nu x w = Finset.univ.sup' (by simp) entry := by
    simp only [polynomialCurvePole]
    rfl
  have hnone : (0 : Real) ≤ polynomialCurvePole nu x w := by
    rw [hpole]
    have hmem : (none : Option (Fin d)) ∈ (Finset.univ : Finset (Option (Fin d))) := by
      simp
    exact Finset.le_sup' entry hmem
  by_cases hpos : 0 < -(polynomialCurveOrder nu (x k) : Real)
  · have hmax : max (-(polynomialCurveOrder nu (x k) : Real)) 0 =
        -(polynomialCurveOrder nu (x k) : Real) := max_eq_left (le_of_lt hpos)
    rw [hmax, hpole]
    have hkmem : (some k : Option (Fin d)) ∈ (Finset.univ : Finset (Option (Fin d))) := by
      simp
    have hle : entry (some k) ≤ Finset.univ.sup' (by simp) entry :=
      Finset.le_sup' entry hkmem
    change -(polynomialCurveOrder nu (x k) : Real) / (w k : Real) ≤ _ at hle
    have := (div_le_iff₀ (hw k)).1 hle
    linarith
  · have : -(polynomialCurveOrder nu (x k) : Real) ≤ 0 := le_of_not_gt hpos
    rw [max_eq_right this]
    exact mul_nonneg (le_of_lt (hw k)) hnone
