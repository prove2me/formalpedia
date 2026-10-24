-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_of_monomials_in_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:49:37.480114+00:00
-- url     : https://prove2.me/submissions/0e2369ec-af9e-4272-b63f-16f14fa5caff

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Finite)
    (hspan : ∀ e : Fin d →₀ Nat,
      MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A S) :
    Module.Finite A (MvPolynomial (Fin d) ℂ) := by
  have htop : Submodule.span A S = ⊤ := by
    apply top_unique
    intro p hp
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro e he
    have h := Submodule.smul_mem (Submodule.span A S)
      (algebraMap ℂ A (MvPolynomial.coeff e p)) (hspan e)
    simpa [Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply ℂ A (MvPolynomial (Fin d) ℂ),
      MvPolynomial.C_mul_monomial] using h
  rw [Module.finite_def]
  rw [← htop]
  exact (Submodule.fg_def).2 ⟨S, hS, rfl⟩