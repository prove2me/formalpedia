-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_finite_weighted_power_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:29:40.261101+00:00
-- url     : https://prove2.me/submissions/372f1c7c-66d6-49c2-bc36-5f5d6c031e49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_curve_bound_gives_span_all_bounded_top_components
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_weighted_power_certificate_of_span_all_bounded

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
        ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
          (∀ j, f j ∈ I ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ k, (w k : Real) * (a k : Real) ≤ D) ∧
          ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
            MvPolynomial.X i ^ e ∈
              Ideal.span (Set.range (fun j =>
                MvPolynomial.weightedHomogeneousComponent
                  (fun k => (w k : Real)) D (f j))) := by
  obtain ⟨s, hs, D, hD, hDR, hspan⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_span_all_bounded_top_components
      I hfinite w hw rho hrho hcurve R hR
  refine ⟨s, hs, D, hD, hDR, ?_⟩
  exact
    OAI.PiExponent.FormalInterpolation.finite_weighted_power_certificate_of_span_all_bounded
      I w s D hspan