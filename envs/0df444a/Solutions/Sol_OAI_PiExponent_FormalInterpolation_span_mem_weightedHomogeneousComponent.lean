-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_mem_weightedHomogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:47:22.921894+00:00
-- url     : https://prove2.me/submissions/11ed6fb4-9e67-45f0-8dbc-c65f1e8fc719

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d m : Nat} (w : Fin d → ℚ) (D : ℚ) (hD : 0 < D)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) D) :
    ∀ f : MvPolynomial (Fin d) ℂ,
      f ∈ Ideal.span (Set.range p) →
      ∀ r : ℚ,
        MvPolynomial.weightedHomogeneousComponent w r f ∈ Ideal.span (Set.range p) := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra ℂ w
  have hspan :
      (Ideal.span (Set.range p)).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule ℂ w) :=
    Ideal.homogeneous_span _ _ (by
      rintro x ⟨j, rfl⟩
      exact ⟨D, (MvPolynomial.mem_weightedHomogeneousSubmodule (R := ℂ) w D (p j)).2 (hp j)⟩)
  intro f hf r
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem (R := ℂ) w hspan hf r