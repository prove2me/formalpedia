-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.con_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:38.698084+00:00
-- url     : https://prove2.me/submissions/95d61753-6705-453a-89bf-56dd63c502ad

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_dec_eq_word
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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (Δ : ASeg T) :
    Con s Δ.start (Δ.len - 1) (Δ.dec s) := by
  rw [dec_eq_word, con_word_iff hs hp]
  exact ⟨0, by have := Δ.len_pos; omega, rfl⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
