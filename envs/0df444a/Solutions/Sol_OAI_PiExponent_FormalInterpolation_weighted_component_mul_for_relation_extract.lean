-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mul_for_relation_extract
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:15:48.652924+00:00
-- url     : https://prove2.me/submissions/41d3625a-b563-4342-9f9f-bf86dab027fa

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_finsum

open MvPolynomial

theorem solution
    {d : Nat} (w : Fin d → ℚ) (D N : ℚ)
    (a b : MvPolynomial (Fin d) ℂ)
    (hb : MvPolynomial.IsWeightedHomogeneous w b D) :
    MvPolynomial.weightedHomogeneousComponent w N (a * b) =
      MvPolynomial.weightedHomogeneousComponent w (N - D) a * b := by
  classical
  rw [OAI.PiExponent.FormalInterpolation.weighted_component_mul_finsum w D N a b hb]
  have hsum :
      (∑ᶠ m : ℚ,
        if m + D = N then
          MvPolynomial.weightedHomogeneousComponent w m a * b else 0) =
        (if (N - D) + D = N then
          MvPolynomial.weightedHomogeneousComponent w (N - D) a * b else 0) := by
    apply finsum_eq_single
    intro m hm
    have hmn : m + D ≠ N := by
      intro h
      apply hm
      linarith
    simp [hmn]
  rw [hsum]
  simp [sub_add_cancel]