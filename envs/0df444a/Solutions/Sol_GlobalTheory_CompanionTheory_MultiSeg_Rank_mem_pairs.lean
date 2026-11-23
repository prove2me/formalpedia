-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:52.334813+00:00
-- url     : https://prove2.me/submissions/454ac8eb-e42b-495c-b124-5d26ae192e77

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Δ : ASeg T} {q : T × ℕ} :
    q ∈ pairs s Δ ↔ Con s q.1 q.2 (Δ.dec s) := by
  unfold pairs
  rw [dec_eq_word, con_word_iff hs hp, Finset.mem_image]
  constructor
  · rintro ⟨⟨d, i⟩, hm, rfl⟩
    have hm' := Finset.mem_sigma.1 hm
    have h1 : d < Δ.len := Finset.mem_range.1 hm'.1
    have h2 : i < Δ.len - d := Finset.mem_range.1 hm'.2
    exact ⟨i, by show i + d < Δ.len; omega, rfl⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨q.2, i⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (by omega : q.2 < Δ.len),
      Finset.mem_range.2 (by omega : i < Δ.len - q.2)⟩, ?_⟩
    exact Prod.ext h rfl
end GlobalTheory.CompanionTheory.MultiSeg.Rank
