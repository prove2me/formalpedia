-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_monic_relations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T22:38:33.152999+00:00
-- url     : https://prove2.me/submissions/4008ec93-3f76-40b4-9f03-0329e9c499ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_weighted_quotient_representatives_with_rounding_margin
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_quotient_representatives_monic_relations_with_rounding_margin

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (a : Rat) (ha : rho < a) :
    ∃ k : Nat, 0 < k ∧ ∃ (b : Fin d → Nat), (∀ i, 0 < b i) ∧
      ∃ (F : Fin d → MvPolynomial (Fin d) Complex),
        (∀ i, F i ∈ I ^ k) ∧
        (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) ∧
        (∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) := by
  obtain ⟨c, hρc, hca, k, hk, hmargin, hrep⟩ :=
    OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_quotient_representatives_with_rounding_margin
      I hfinite w hw rho hrho hcurve a ha
  have hc : 0 < c := lt_of_le_of_lt hrho hρc
  exact OAI.PiExponent.FormalInterpolation.weighted_quotient_representatives_monic_relations_with_rounding_margin
    I w hw c a hc hca k hk hmargin hrep