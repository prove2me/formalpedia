-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_at_infinity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:14:32.987951+00:00
-- url     : https://prove2.me/submissions/6a59edc9-a6cd-4feb-8d72-f3518e2fc9c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_power_sections_asymptotic_initial_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_initial_power_witness_extraction

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (R : Real) (hR : (rho : Real) < R) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
          (∀ j, f j ∈ I ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
          (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
            MvPolynomial.X i ^ e ∈
              Ideal.span (Set.range (fun j : Fin k =>
                MvPolynomial.weightedHomogeneousComponent
                  (fun i => (w i : Real)) D (f j)))) := by
  obtain ⟨s, hs, D, hD, hDR, hinitial⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_power_sections_asymptotic_initial_power
      I hfinite w hw rho hrho hcurve R hR
  refine ⟨s, hs, D, hD, hDR, ?_⟩
  exact
    OAI.PiExponent.FormalInterpolation.finite_initial_power_witness_extraction
      I w s hs D hD hinitial