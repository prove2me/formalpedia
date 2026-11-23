-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.mem_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:20.419281+00:00
-- url     : https://prove2.me/submissions/06004d4f-6380-4cfb-862f-729d33c8aaf7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt

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
theorem _root_.solution {s : T → T} {t y : T} {l : ℕ} : y ∈ word s t l ↔ ∃ i < l, s^[i] t = y := by
  simp only [word, List.mem_map, List.mem_reverse, List.mem_range]
end GlobalTheory.CompanionTheory.MultiSeg.Rank
