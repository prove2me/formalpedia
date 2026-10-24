-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_pointwise_sections_20261023_22
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:43:43.555238+00:00
-- url     : https://prove2.me/submissions/e5cd0da1-9dcc-4e1b-a316-14b440f4f842
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_initial_ideal_pointwise
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_initial_ideal_powers

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * ((rho : Real) + eps) ∧ 0 < D ∧
      ∀ x : Fin d → Complex,
        (∃ i : Fin d, x i ≠ 0) →
        ∃ g : MvPolynomial (Fin d) Complex,
          g ∈ I ^ s ∧
          (∀ a ∈ g.support,
            ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0 := by
  obtain ⟨s, hs, D, hD, hDpos, hcoords⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_initial_ideal_powers
      I hfinite w hw rho hrho hcurve eps heps
  refine ⟨s, hs, D, hD, hDpos, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.bounded_initial_ideal_pointwise
    I w s D hs hDpos hcoords