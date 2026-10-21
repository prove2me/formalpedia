-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:22:22.9836+00:00
-- url     : https://prove2.me/submissions/6c66838c-1f30-402f-9ef9-3e1a388873d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_weighted_monic_relations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_monic_relations_eventual_representatives

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (delta : Rat) (hdelta : rho < delta) :
    ∃ n₀ : Nat, ∀ n : Nat, n₀ ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * (delta : Real) := by
  -- Pick an intermediate rate strictly between rho and delta.
  set a : Rat := (rho + delta) / 2 with hadef
  have hrhoa : rho < a := by rw [hadef]; linarith
  have hadelta : a < delta := by rw [hadef]; linarith
  have ha0 : 0 < a := lt_of_le_of_lt hrho hrhoa
  -- The geometric step: weighted monic relations below the intermediate rate.
  obtain ⟨k, hk, b, hb, F, hF, hbelow, hbudget⟩ :=
    OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_monic_relations
      I hfinite w hw rho hrho hcurve a hrhoa
  -- The algebraic step: weighted division gives representatives at rate delta.
  exact OAI.PiExponent.FormalInterpolation.weighted_monic_relations_eventual_representatives
    I w hw k hk b hb F hF hbelow a delta ha0 hadelta hbudget
