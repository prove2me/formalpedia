-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_relations_span_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:48:43.312467+00:00
-- url     : https://prove2.me/submissions/c1b716f9-3d07-48a9-8960-06dfb8a3c319

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    (d m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (N : Fin d → Nat)
    (hpower : ∀ i, ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i = ∑ j, q j * p j) :
    Ideal.span (Set.range (fun i : Fin d =>
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i)) ≤
    Ideal.span (Set.range p) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i ∈
    Ideal.span (Set.range p)
  obtain ⟨q, hq⟩ := hpower i
  rw [hq]
  apply Ideal.sum_mem
  intro j hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)