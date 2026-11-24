-- Prove2me | solution 1 for GlobalTheory.dvd_of_dvd_mul_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:09.537227+00:00
-- url     : https://prove2.me/submissions/746b6502-7abd-4d63-a417-fc4115e71f83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (t u : A) (h : ∀ F : A, t ∣ u * F → t ∣ F) (x : B)
    (hx : algebraMap A B t ∣ algebraMap A B u * x) : algebraMap A B t ∣ x := by
  have hm : IsSMulRegular (A ⧸ Ideal.span {t}) u := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    apply h
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  have hJ : ∀ y : B, algebraMap A B t ∣ y ↔ y ∈ (Ideal.span {t}).map (algebraMap A B) := by
    intro y
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  rw [hJ] at hx ⊢
  have h := hm.lTensor B
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {t})
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply e.injective
  rw [map_zero]
  apply h
  have h2 := congrArg e hx
  rw [map_zero] at h2
  simp only [smul_zero]
  rw [← h2, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, TensorProduct.smul_tmul',
    Algebra.smul_def]
end GlobalTheory
