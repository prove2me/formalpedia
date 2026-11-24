-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:43.586209+00:00
-- url     : https://prove2.me/submissions/76badc45-21d0-471b-b15c-1fe2bd261fa1

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
theorem _root_.solution (l : ℕ) : ∑ d ∈ Finset.range (l + 1), wd d = 2 * l + 1 := by
  induction l with
  | zero => simp [wd]
  | succ l ih =>
    rw [Finset.sum_range_succ, ih, wd, if_neg (Nat.succ_ne_zero l)]
    ring
end GlobalTheory.CompanionTheory.MultiSeg.Rank
