-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mul
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:28:26.494622+00:00
-- url     : https://prove2.me/submissions/2a2909b0-7277-44c3-8ff0-ba5ca8a870d8

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_as_sum

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Real) (D E : Real)
    (q f : MvPolynomial (Fin d) Complex)
    (hf : MvPolynomial.IsWeightedHomogeneous w f D) :
    MvPolynomial.weightedHomogeneousComponent w E (q * f) =
      MvPolynomial.weightedHomogeneousComponent w (E - D) q * f := by
  classical
  rw [OAI.PiExponent.FormalInterpolation.weighted_component_mul_as_sum (hf := hf)]
  calc
    _ = (if (E - D) + D = E then
          MvPolynomial.weightedHomogeneousComponent w (E - D) q * f else 0) :=
      Finset.sum_eq_single_of_mem (a := E - D) (by simp) (by
        intro a ha hne
        have hweight : a + D ≠ E := by
          intro h
          apply hne
          linarith
        simp [hweight])
    _ = MvPolynomial.weightedHomogeneousComponent w (E - D) q * f := by simp