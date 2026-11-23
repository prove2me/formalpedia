-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.isCMType_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:24.495681+00:00
-- url     : https://prove2.me/submissions/36bd42ea-7f77-4caf-b76f-2bb74309ce28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution : IsCMType (fun w : InfinitePlace E => w.embedding) := by
  intro σ
  refine ⟨InfinitePlace.mk σ, ?_, ?_⟩
  · rcases InfinitePlace.embedding_mk_eq σ with h | h
    · exact Or.inl h.symm
    · right; simp only [h]; ext x; simp
  · rintro w (h | h)
    · rw [h, InfinitePlace.mk_embedding]
    · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
end GlobalTheory.CMVal.InhabK
