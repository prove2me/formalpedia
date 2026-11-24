-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.con_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:36.692332+00:00
-- url     : https://prove2.me/submissions/70553606-dc93-4577-ace6-a805f0a50ef0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_word_iff

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
theorem _root_.solution {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {u t : T} {d j l : ℕ}
    (h : Con s u d (word s t l)) (hj : j ≤ d) : Con s u j (word s t l) := by
  rw [con_word_iff hs hp] at h ⊢
  obtain ⟨i, hi, hu⟩ := h
  exact ⟨i, by omega, hu⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
