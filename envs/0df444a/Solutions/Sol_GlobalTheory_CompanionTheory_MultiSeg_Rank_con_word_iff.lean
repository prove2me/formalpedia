-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.con_word_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.332403+00:00
-- url     : https://prove2.me/submissions/5ac263ce-f031-4730-9948-f5ac77436e3d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_iter_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_word

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {u t : T} {d l : ℕ} :
    Con s u d (word s t l) ↔ ∃ i, i + d < l ∧ s^[i] t = u := by
  unfold Con
  rw [mem_word, mem_word]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, ⟨k, hk, hk'⟩⟩
    refine ⟨i, ?_, rfl⟩
    rw [← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega, rfl⟩, ⟨d + i, by omega, Function.iterate_add_apply s d i t⟩⟩
end GlobalTheory.CompanionTheory.MultiSeg.Rank
