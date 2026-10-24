-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_bounded_family_from_curve_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:43:10.434778+00:00
-- url     : https://prove2.me/submissions/b48910c4-d885-4962-9239-71b02b480b44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_bounded_power_system
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_weighted_top_components

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat, (D : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
        (∀ j, g j ∈ I ^ s) ∧
        (∀ j, ∀ a ∈ (g j).support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        Module.Finite (Algebra.adjoin Complex (Set.range g))
          (MvPolynomial (Fin d) Complex) := by
  obtain ⟨s, hs, D, hD, hDpos, m, g, hg, hbound, htop⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_bounded_power_system
      I hfinite w hw rho hrho hcurve eps heps
  have hfiniteAlg :=
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_weighted_top_components
      w hw D hDpos m g hbound htop
  exact ⟨s, hs, D, hD, m, g, hg, hbound, hfiniteAlg⟩