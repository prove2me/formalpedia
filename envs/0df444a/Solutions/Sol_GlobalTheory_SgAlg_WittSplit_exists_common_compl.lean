-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.exists_common_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:00:00.432081+00:00
-- url     : https://prove2.me/submissions/0291aa59-0f0a-4c2a-90f5-3045966024df

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_not_mem_both
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_finrank_sup_singleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution : ∀ (d : ℕ) (U U' : Submodule K V), finrank K V - finrank K U = d →
    finrank K U = finrank K U' → ∃ S : Submodule K V, IsCompl U S ∧ IsCompl U' S := by
  intro d
  induction d with
  | zero =>
    intro U U' hd h
    have hU : U = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le U) (by omega))
    have hU' : U' = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le U') (by have := Submodule.finrank_le U; omega))
    exact ⟨⊥, hU ▸ isCompl_top_bot, hU' ▸ isCompl_top_bot⟩
  | succ d ih =>
    intro U U' hd h
    have hU : U ≠ ⊤ := by
      rintro rfl; simp [finrank_top] at hd
    obtain ⟨v, hv, hv'⟩ := exists_not_mem_both U U' h hU
    obtain ⟨S1, hS1, hS1'⟩ := ih (U ⊔ K ∙ v) (U' ⊔ K ∙ v)
      (by rw [finrank_sup_singleton U hv]; omega)
      (by rw [finrank_sup_singleton U hv, finrank_sup_singleton U' hv', h])
    refine ⟨(K ∙ v) ⊔ S1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (Submodule.disjoint_span_singleton_of_notMem hv).disjoint_sup_right_of_disjoint_sup_left
        hS1.disjoint
    · rw [codisjoint_iff, ← sup_assoc]; exact codisjoint_iff.1 hS1.codisjoint
    · exact (Submodule.disjoint_span_singleton_of_notMem hv').disjoint_sup_right_of_disjoint_sup_left
        hS1'.disjoint
    · rw [codisjoint_iff, ← sup_assoc]; exact codisjoint_iff.1 hS1'.codisjoint
end GlobalTheory.SgAlg.WittSplit
