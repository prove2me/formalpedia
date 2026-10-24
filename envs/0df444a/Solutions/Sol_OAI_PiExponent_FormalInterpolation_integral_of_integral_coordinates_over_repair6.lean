-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integral_of_integral_coordinates_over_repair6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:53.489616+00:00
-- url     : https://prove2.me/submissions/9aa3a210-eb45-4b1c-b4fa-02f5c8defdba

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib

open OAI.PiExponent.FormalInterpolation

open MeasureTheory Filter Topology in

theorem solution
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    ∀ x : MvPolynomial (Fin d) Complex, IsIntegral A x := by
  intro x
  induction x using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial (Fin d) Complex) =
        algebraMap A _ ⟨MvPolynomial.C a, A.algebraMap_mem a⟩ := rfl
    rw [this]; exact isIntegral_algebraMap
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (hcoords i)
