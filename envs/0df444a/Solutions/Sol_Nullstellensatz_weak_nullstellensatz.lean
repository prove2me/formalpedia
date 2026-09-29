-- Prove2me | solution 1 for Nullstellensatz.weak_nullstellensatz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:52:39.202925+00:00
-- url     : https://prove2.me/submissions/8951e0c1-b423-4345-a4ba-9aafcf7d5daa

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem aux_wn_main {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (hJ : J ≠ ⊤) :
    ∃ a : Fin n → K, ∀ f ∈ J, aeval a f = 0 := by
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  let _ : Field (MvPolynomial (Fin n) k ⧸ m) := Ideal.Quotient.field m
  have _ : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ m) := inferInstance
  have _ : Module.Finite k (MvPolynomial (Fin n) k ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k _
  have _ : Algebra.IsAlgebraic k (MvPolynomial (Fin n) k ⧸ m) := inferInstance
  let φ : (MvPolynomial (Fin n) k ⧸ m) →ₐ[k] K := IsAlgClosed.lift
  let ψ : MvPolynomial (Fin n) k →ₐ[k] K := φ.comp (Ideal.Quotient.mkₐ k m)
  refine ⟨fun i => ψ (X i), fun f hf => ?_⟩
  have h1 : aeval (fun i => ψ (X i)) f = ψ f := by
    conv_rhs => rw [MvPolynomial.aeval_unique ψ]
    rfl
  rw [h1]
  show φ (Ideal.Quotient.mkₐ k m f) = 0
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm hf), map_zero]

end Nullstellensatz

open Nullstellensatz

theorem solution {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (hJ : J ≠ ⊤) :
    ∃ a : Fin n → K, ∀ f ∈ J, aeval a f = 0 :=
  aux_wn_main J hJ
