-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_finite_sections
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:32:39.241761+00:00
-- url     : https://prove2.me/submissions/c057d14f-606d-4145-bc4d-3bbb35c5b069
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinatewise_curve_bounded_sections
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_synchronize_coordinatewise_sections

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ (s : Nat) (S : Finset (MvPolynomial (Fin d) Complex)),
      0 < s ∧
      (∀ f ∈ S, f ∈ I ^ s) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by
  apply OAI.PiExponent.FormalInterpolation.synchronize_coordinatewise_sections
  intro i
  exact OAI.PiExponent.FormalInterpolation.coordinatewise_curve_bounded_sections
    I hfinite w hw rho hrho hcurve eps heps i