-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_individual_coordinate_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:26:49.559165+00:00
-- url     : https://prove2.me/submissions/f0d5839c-1b66-4a66-83c9-cb9e1aa8662e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_finite_sections
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_sections_span_transfer

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∀ i : Fin d, ∃ s n : Nat, 0 < s ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by
  obtain ⟨s, S, hs, hS, hcoordinates⟩ :=
    curve_bound_finite_sections I hfinite w hw rho hrho hcurve eps heps
  exact bounded_sections_span_transfer I s S hS w rho eps hcoordinates