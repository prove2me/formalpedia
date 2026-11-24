-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exists_infExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:52.792834+00:00
-- url     : https://prove2.me/submissions/970f6362-e198-4221-8fd1-98c9d5152ce4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (φ : E →+* ℂ) :
    ∃ e : InfiniteAdeleRing E →+* ℂ, Continuous e ∧ (∀ k : E, e (algebraMap E _ k) = φ k) ∧
      ∀ x y : InfiniteAdeleRing E, x (InfinitePlace.mk φ) = y (InfinitePlace.mk φ) → e x = e y := by
  have h0 : ∀ k : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap E _ k) =
      (InfinitePlace.mk φ).embedding k := fun k =>
    InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  let e : InfiniteAdeleRing E →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)).comp (Pi.evalRingHom _ (InfinitePlace.mk φ))
  have he : Continuous e := hc.comp (continuous_apply _)
  have h1 : ∀ k, e (algebraMap E _ k) = (InfinitePlace.mk φ).embedding k := h0
  have h2 : ∀ x y : InfiniteAdeleRing E, x (InfinitePlace.mk φ) = y (InfinitePlace.mk φ) → e x = e y := fun x y h =>
    congrArg (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)) h
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨e, he, fun k => by rw [h1, h], h2⟩
  · refine ⟨(starRingEnd ℂ).comp e, Complex.continuous_conj.comp he, fun k => ?_,
      fun x y h => congrArg (starRingEnd ℂ) (h2 x y h)⟩
    rw [RingHom.comp_apply, h1, h]
    simp
end GlobalTheory.CMVal.ValEx
