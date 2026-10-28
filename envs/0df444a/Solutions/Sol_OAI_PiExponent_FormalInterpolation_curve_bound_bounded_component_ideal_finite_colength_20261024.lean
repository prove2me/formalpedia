-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_component_ideal_finite_colength_20261024
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:14:49.615802+00:00
-- url     : https://prove2.me/submissions/5334e780-77ab-43b0-ab5f-37ac5e4f0b95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_low_slope_coordinate_relations_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_component_from_low_slope_coordinate_relations_20261024
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
      Module.Finite Complex
        (MvPolynomial (Fin d) Complex ⧸ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧ ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1))) := by
  obtain ⟨s, hs, q, hq, hgap, n, hn, hdegree, f, hrelation, hsupport⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_low_slope_coordinate_relations_20261024
      I hfinite w hw rho hrho hcurve eps heps
  exact
    OAI.PiExponent.FormalInterpolation.bounded_component_from_low_slope_coordinate_relations_20261024
      I w rho eps s hs q hq hgap n hn hdegree f hrelation hsupport