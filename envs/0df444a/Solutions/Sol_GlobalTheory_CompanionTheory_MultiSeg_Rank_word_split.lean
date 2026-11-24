-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.word_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:10:27.551916+00:00
-- url     : https://prove2.me/submissions/356166de-e3fd-4496-ace8-1e11f25cb848

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_word_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_word_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
theorem _root_.solution (s : T → T) (t : T) : ∀ (l : ℕ) (a b : List T), word s t l = a ++ b →
    ∃ l', l' ≤ l ∧ b = word s t l' ∧ ∀ y ∈ a, ∃ i, l' ≤ i ∧ i < l ∧ s^[i] t = y := by
  intro l
  induction l with
  | zero =>
    intro a b h
    rw [word_zero] at h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
    exact ⟨0, le_refl 0, (word_zero s t).symm, fun y hy => by simp at hy⟩
  | succ l ih =>
    intro a b h
    cases a with
    | nil =>
      refine ⟨l + 1, le_refl _, ?_, fun y hy => by simp at hy⟩
      simpa using h.symm
    | cons y a' =>
      rw [word_succ, List.cons_append] at h
      obtain ⟨hy, h'⟩ := List.cons.inj h
      obtain ⟨l', hl', hb, ha⟩ := ih a' b h'
      refine ⟨l', Nat.le_succ_of_le hl', hb, ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨l, hl', Nat.lt_succ_self l, hy⟩
      · obtain ⟨i, h1, h2, h3⟩ := ha z hz
        exact ⟨i, h1, Nat.lt_succ_of_lt h2, h3⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
