-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegOrder.exists_sublists_interleave
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:47.765443+00:00
-- url     : https://prove2.me/submissions/00f7c392-55e3-4e07-a5d0-e267cb7126d1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCommonOrderedForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_Interleave_append_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_Interleave_append_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_wt_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegOrder
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.SegOrder
theorem _root_.solution (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  classical
  induction L with
  | nil =>
    intro m n h
    have h0 : m = 0 ∧ n = 0 := add_eq_zero.1 (by simpa using h.symm)
    refine ⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩
    · simp [h0.1]
    · simp [h0.2]
  | cons a L ih =>
    intro m n h
    have ha : a ∈ m + n := by
      rw [← h]
      simp
    rcases Multiset.mem_add.1 ha with ha | ha
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih (m.erase a) n hL
      refine ⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩
      · rw [← Multiset.cons_coe, e₁, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih m (n.erase a) hL
      refine ⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩
      · rw [← Multiset.cons_coe, e₂, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _
end GlobalTheory.CompanionTheory.SegOrder
