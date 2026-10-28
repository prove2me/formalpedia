-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_initial_components_with_slack
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T08:45:54.843394+00:00
-- url     : https://prove2.me/submissions/a50f2d7e-2fb0-4513-9442-41f4e191e3a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_initial_component_finite_colength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_homogeneous_finite_colength_coordinate_powers
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1)) := by
  obtain ⟨s, hs, q, hq, hbound, hfiniteK⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_initial_component_finite_colength
      I hfinite w hw rho hrho hcurve eps heps
  refine ⟨s, hs, q, hq, hbound, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.weighted_homogeneous_finite_colength_coordinate_powers
    I w hw s q hq hfiniteK
