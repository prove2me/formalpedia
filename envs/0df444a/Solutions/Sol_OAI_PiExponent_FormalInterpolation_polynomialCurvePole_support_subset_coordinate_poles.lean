-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurvePole_support_subset_coordinate_poles
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:42:28.722909+00:00
-- url     : https://prove2.me/submissions/4810a270-4df8-41d3-8c96-4a763b8fee0e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (x : Fin d → E) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) :
    {nu : PolynomialCurvePlace E | polynomialCurvePole nu x w ≠ 0} ⊆
      ⋃ j : Fin d, {nu | max (-(polynomialCurveOrder nu (x j) : Real)) 0 ≠ 0} := by
  classical
  intro nu hnu
  let entry : Option (Fin d) → Real :=
    fun i => i.elim 0 (fun j => -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))
  have hpole : polynomialCurvePole nu x w = Finset.univ.sup' (by simp) entry := by
    simp only [polynomialCurvePole]; rfl
  have hnone : 0 ≤ polynomialCurvePole nu x w := by
    rw [hpole]
    exact Finset.le_sup' entry (by simp : (none : Option (Fin d)) ∈ Finset.univ)
  have hpole_pos : 0 < polynomialCurvePole nu x w :=
    lt_of_le_of_ne hnone (Ne.symm hnu)
  obtain ⟨i, _hi, hieq⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Option (Fin d)))) (by simp) entry
  have hentry : entry i = polynomialCurvePole nu x w := by rw [hpole, hieq]
  match i with
  | none =>
      change (0 : Real) = polynomialCurvePole nu x w at hentry
      linarith
  | some j =>
      have heq : -(polynomialCurveOrder nu (x j) : Real) / (w j : Real) =
          polynomialCurvePole nu x w := by simpa [entry] using hentry
      have hneg : 0 < -(polynomialCurveOrder nu (x j) : Real) := by
        have hwpos := hw j
        have hrewrite :
            -(polynomialCurveOrder nu (x j) : Real) =
              polynomialCurvePole nu x w * (w j : Real) := by
          calc
            -(polynomialCurveOrder nu (x j) : Real)
                = (-(polynomialCurveOrder nu (x j) : Real) / (w j : Real)) *
                    (w j : Real) := by field_simp
            _ = polynomialCurvePole nu x w * (w j : Real) := by rw [heq]
        nlinarith [hpole_pos, hwpos, hrewrite]
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      have : 0 < max (-(polynomialCurveOrder nu (x j) : Real)) 0 := by
        rwa [max_eq_left (le_of_lt hneg)]
      exact this.ne'
