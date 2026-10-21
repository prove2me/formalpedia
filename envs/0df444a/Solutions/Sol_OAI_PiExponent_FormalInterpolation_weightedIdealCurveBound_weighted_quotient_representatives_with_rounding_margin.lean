-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_quotient_representatives_with_rounding_margin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T22:50:04.219513+00:00
-- url     : https://prove2.me/submissions/eb139f29-00ea-4c60-aeae-980cf9f0b711
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_eventual_quotient_representatives_with_rounding_margin_core
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_large_power_with_rounding_margin

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (a : Rat) (ha : rho < a) :
    ∃ c : Rat, rho < c ∧ c < a ∧
      ∃ k : Nat, 0 < k ∧
        (∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real)) ∧
        ∀ P : MvPolynomial (Fin d) Complex,
          ∃ R : MvPolynomial (Fin d) Complex,
            P - R ∈ I ^ k ∧
            ∀ v ∈ R.support,
              (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real) := by
  obtain ⟨c, hρc, hca, N, hrep⟩ :=
    OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives_with_rounding_margin_core
      I hfinite w hw rho hrho hcurve a ha
  obtain ⟨k, hkpos, hkN, hmargin⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_large_power_with_rounding_margin
      w hw a c hca N
  refine ⟨c, hρc, hca, k, hkpos, hmargin, ?_⟩
  intro P
  exact hrep k hkN hmargin P
