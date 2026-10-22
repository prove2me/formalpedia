-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_implies_eventual_weighted_generation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T08:51:44.618634+00:00
-- url     : https://prove2.me/submissions/342182dc-b5df-4376-949f-8b128574f7be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_implies_strict_slope_representatives

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (fun q : {q : MvPolynomial (Fin d) Complex //
              ∀ a ∈ q.support,
                ∑ i, (w i : Real) * (a i : Real) ≤
                  (n : Real) * ((rho : Real) + eps)} =>
          Ideal.Quotient.mk (I ^ n) q.1) := by
  obtain ⟨delta, _, hdelta, N, hN⟩ :=
    OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_implies_strict_slope_representatives
      I hfinite w hw rho hrho hcurve eps heps
  refine ⟨N, ?_⟩
  intro n hn z
  obtain ⟨q, hq, hbound⟩ := hN n hn z
  refine ⟨⟨q, ?_⟩, hq⟩
  intro a ha
  exact (hbound a ha).trans
    (mul_le_mul_of_nonneg_left hdelta.le (Nat.cast_nonneg n))
