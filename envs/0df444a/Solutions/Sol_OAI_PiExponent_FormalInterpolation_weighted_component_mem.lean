-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:56:07.883172+00:00
-- url     : https://prove2.me/submissions/d5bdcb4c-513e-42c4-88b2-49b6dceaad07

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_eq_directSum_decompose

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ)
    [GradedRing (MvPolynomial.weightedHomogeneousSubmodule ℂ w)]
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w))
    {f : MvPolynomial (Fin d) ℂ} (hf : f ∈ I) (r : ℚ) :
    MvPolynomial.weightedHomogeneousComponent w r f ∈ I := by
  rw [OAI.PiExponent.FormalInterpolation.weighted_component_eq_directSum_decompose]
  exact hI r hf