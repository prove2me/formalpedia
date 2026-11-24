-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegOrder.exists_last_start
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:14.060069+00:00
-- url     : https://prove2.me/submissions/184ca652-475b-4bdc-ba5b-fea049ff6f06

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm

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
theorem _root_.solution (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by
  have irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start := by
    rintro a ⟨j, hj, h⟩
    exact hs a.start j hj h.symm
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons x m ih =>
    by_cases hm' : m = 0
    · subst hm'
      refine ⟨x, Multiset.mem_cons_self x 0, ?_⟩
      intro b hb
      have hbx : b = x := by simpa using hb
      subst hbx
      exact irr b
    · obtain ⟨a, ham, hmax⟩ := ih hm'
      by_cases hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start
      · obtain ⟨j, hj, hxa⟩ := hax
        refine ⟨x, Multiset.mem_cons_self x m, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact irr b
        · rintro ⟨i, hi, hbx⟩
          refine hmax b hbm ⟨i + j, by omega, ?_⟩
          rw [hbx, hxa, Function.iterate_add_apply]
      · refine ⟨a, Multiset.mem_cons_of_mem ham, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact hax
        · exact hmax b hbm
end GlobalTheory.CompanionTheory.SegOrder
