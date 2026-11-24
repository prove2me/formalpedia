-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.con_suffix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:44.962391+00:00
-- url     : https://prove2.me/submissions/e5c8c9d4-9448-4084-aacc-b3210304aee7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_iter_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_word_split

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {a b : List T} {t : T} {l : ℕ}
    (hx : a ++ b = word s t l) {u : T} {d : ℕ} (hc : Con s u d (a ++ b))
    (hv : s^[d] u ∉ a) : Con s u d b := by
  obtain ⟨l', _, hb, ha⟩ := word_split s t l a b hx.symm
  have hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b := hc
  have hvb : s^[d] u ∈ b := by
    rcases List.mem_append.1 hc'.2 with h | h
    · exact absurd h hv
    · exact h
  show u ∈ b ∧ s^[d] u ∈ b
  refine ⟨?_, hvb⟩
  rcases List.mem_append.1 hc'.1 with h | h
  · exfalso
    obtain ⟨i, hi1, _, hi3⟩ := ha u h
    rw [hb, mem_word] at hvb
    obtain ⟨k, hk, hk'⟩ := hvb
    rw [← hi3, ← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega
  · exact h
end GlobalTheory.CompanionTheory.MultiSeg.Rank
