-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_coordinate_powers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:18:09.405663+00:00
-- url     : https://prove2.me/submissions/65252abb-d3c5-4f84-b977-a6da60ff121c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_individual_coordinate_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_synchronize_coordinate_power_witnesses

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real) := by
  have hhalf : 0 < eps / 2 := div_pos heps two_pos
  have hcoord :=
    OAI.PiExponent.FormalInterpolation.curve_bound_individual_coordinate_power
      I hfinite w hw rho hrho hcurve (eps / 2) hhalf
  exact
    OAI.PiExponent.FormalInterpolation.synchronize_coordinate_power_witnesses
      I w hw rho hrho eps heps hcoord