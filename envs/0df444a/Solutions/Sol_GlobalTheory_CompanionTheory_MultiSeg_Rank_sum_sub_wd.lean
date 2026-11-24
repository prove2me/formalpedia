-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_sub_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:10.420604+00:00
-- url     : https://prove2.me/submissions/249b90d9-c031-4337-90d0-5793debcb7a3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sum_wd

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
theorem _root_.solution (l : ℕ) : ∑ d ∈ Finset.range l, (l - d) * wd d = l ^ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h1 : ∑ d ∈ Finset.range (l + 1), (l + 1 - d) * wd d =
        ∑ d ∈ Finset.range (l + 1), ((l - d) * wd d + wd d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have : d < l + 1 := Finset.mem_range.1 hd
      rw [show l + 1 - d = (l - d) + 1 by omega, Nat.add_mul, one_mul]
    rw [h1, Finset.sum_add_distrib, sum_wd, Finset.sum_range_succ, ih, Nat.sub_self, zero_mul,
      add_zero]
    ring
end GlobalTheory.CompanionTheory.MultiSeg.Rank
