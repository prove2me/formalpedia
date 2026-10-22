-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_surjective_weighted_sections
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:09:14.631118+00:00
-- url     : https://prove2.me/submissions/d16dcd70-1795-4c71-8a9c-0e57558bd52a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_implies_eventual_weighted_generation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_generation_implies_eventual_surjective_weighted_sections

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
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) := by
  have hgen :=
    weightedIdealCurveBound_implies_eventual_weighted_generation
      I hfinite w hw rho hrho hcurve eps heps
  exact eventual_weighted_generation_implies_eventual_surjective_weighted_sections
    I w rho eps hgen
