-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_asymptotic_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:04:15.842947+00:00
-- url     : https://prove2.me/submissions/5b0db196-a6e2-4197-b332-e56a2b908728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_eventual_surjective_weighted_sections
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_asymptotic_representatives_of_eventual_weighted_surjectivity

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ C : Nat, ∀ n : Nat, ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) + (C : Real) := by
  -- Geometric core: curve bound ⇒ eventual surjectivity of weight ≤ n(ρ+ε) sections.
  have heventual :=
    weightedIdealCurveBound_eventual_surjective_weighted_sections
      I hfinite w hw rho hrho hcurve eps heps
  -- Algebraic absorption: eventual bound ⇒ uniform additive constant for all n
  -- via I^N ⊆ I^n for n < N and C = ⌈N(ρ+ε)⌉₊.
  exact asymptotic_representatives_of_eventual_weighted_surjectivity
    I w rho hrho eps heps heventual
