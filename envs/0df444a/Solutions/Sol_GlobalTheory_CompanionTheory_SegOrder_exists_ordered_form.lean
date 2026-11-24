-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegOrder.exists_ordered_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:16.009233+00:00
-- url     : https://prove2.me/submissions/bbf803c9-abc9-4cf3-b2c9-2aa4fb2bc3f2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_exists_last_start

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
theorem _root_.solution : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by
  classical
  intro T s _ hs m
  induction hn : Multiset.card m generalizing m with
  | zero =>
    refine ⟨[], ?_, List.Pairwise.nil⟩
    simpa using (Multiset.card_eq_zero.mp hn).symm
  | succ n ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    obtain ⟨a, ham, hmax⟩ := exists_last_start s hs m hm
    have hcard : Multiset.card (m.erase a) = n := by
      rw [Multiset.card_erase_of_mem ham, hn]
      rfl
    obtain ⟨L, hL, hord⟩ := ih (m.erase a) hcard
    refine ⟨a :: L, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hL]
      exact Multiset.cons_erase ham
    · refine List.pairwise_cons.mpr ⟨?_, hord⟩
      intro b hb hprec
      have hbm : b ∈ m := by
        have : b ∈ (L : Multiset (ASeg T)) := by simpa using hb
        rw [hL] at this
        exact Multiset.mem_of_mem_erase this
      exact hmax b hbm hprec.2
end GlobalTheory.CompanionTheory.SegOrder
