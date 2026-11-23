-- Prove2me | solution 1 for GlobalTheory.SimilarTranspose.exists_bilin_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:08.406271+00:00
-- url     : https://prove2.me/submissions/b005035b-26b6-4a2f-98b0-89c90ad2ad26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
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
open GlobalTheory GlobalTheory.SimilarTranspose
namespace GlobalTheory.SimilarTranspose
theorem _root_.solution {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ ∀ y, (∀ x, B x y = 0) → y = 0 := by
  obtain ⟨l, h1, h2⟩ := exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  have hl : ∀ a, l' (Ideal.Quotient.mk _ a) = l a := fun a => rfl
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_⟩
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
end GlobalTheory.SimilarTranspose
