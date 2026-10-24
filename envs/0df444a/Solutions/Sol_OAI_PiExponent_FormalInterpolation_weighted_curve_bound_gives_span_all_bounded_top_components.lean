-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_curve_bound_gives_span_all_bounded_top_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:35:38.350158+00:00
-- url     : https://prove2.me/submissions/913d0d7e-6b6a-42f5-b202-944b60e3a30b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_bounded_weight_quotient_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_representatives_give_span_all_bounded_top_components

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
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun f :
              {p : MvPolynomial (Fin d) Complex //
                p ∈ I ^ s ∧
                ∀ a ∈ p.support,
                  ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : Real)) D f.1)) := by
  obtain ⟨cut, hcut, hcutR⟩ := exists_between hR
  have hdelta : 0 < cut - (rho : Real) := by linarith
  have hrate : (rho : Real) + (cut - (rho : Real)) < R := by linarith
  obtain ⟨C, hC, N, hrepr⟩ :=
    OAI.PiExponent.FormalInterpolation.eventual_bounded_weight_quotient_representatives
      I hfinite w hw rho hrho hcurve (cut - (rho : Real)) hdelta
  exact OAI.PiExponent.FormalInterpolation.quotient_representatives_give_span_all_bounded_top_components
    I w hw rho hrho R hR (cut - (rho : Real)) hdelta C hC N hrate hrepr