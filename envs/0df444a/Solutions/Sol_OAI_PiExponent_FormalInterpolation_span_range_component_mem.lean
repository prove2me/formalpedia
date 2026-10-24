-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_range_component_mem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:41:50.284348+00:00
-- url     : https://prove2.me/submissions/66417478-1ef0-45b4-8896-8a57206210ed

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (D : Nat)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (f : MvPolynomial (Fin d) ℂ)
    (hf : f ∈ Ideal.span (Set.range p)) (a : ℚ) :
    MvPolynomial.weightedHomogeneousComponent w a f ∈ Ideal.span (Set.range p) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ w) :=
    MvPolynomial.weightedGradedAlgebra ℂ w
  have hI : (Ideal.span (Set.range p)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ w) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact ⟨(D : ℚ), hp j⟩
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℂ w hI hf a