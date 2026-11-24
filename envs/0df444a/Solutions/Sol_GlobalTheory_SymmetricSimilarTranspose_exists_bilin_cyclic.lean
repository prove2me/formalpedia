-- Prove2me | solution 1 for GlobalTheory.SymmetricSimilarTranspose.exists_bilin_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:00:00.590722+00:00
-- url     : https://prove2.me/submissions/d2f15a60-da25-44fb-b234-1182037b6286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhaus
import Theorems.Thm_GlobalTheory_SimilarTranspose_exists_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SymmetricSimilarTranspose
namespace GlobalTheory.SymmetricSimilarTranspose
theorem _root_.solution {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        ∀ x y, B x y = B y x := by
  obtain ⟨l, h1, h2⟩ := GlobalTheory.SimilarTranspose.exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l
      (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l ((X * a) * b) = l (a * (X * b))
    congr 1; ring
  · intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))
    have := hy (Ideal.Quotient.mk (Ideal.span {f}) a)
    rw [mul_comm]
    exact this
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l (a * b) = l (b * a)
    rw [mul_comm]
end GlobalTheory.SymmetricSimilarTranspose
