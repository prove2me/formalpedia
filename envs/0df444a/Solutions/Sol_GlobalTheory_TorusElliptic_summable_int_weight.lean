-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.summable_int_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:06.310249+00:00
-- url     : https://prove2.me/submissions/418b16ae-67be-447c-a0e6-dd4e06039246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.TorusElliptic
namespace GlobalTheory.TorusElliptic
theorem _root_.solution : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h : Summable (fun j : ℕ => 1 / (1 + (j : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine this.congr fun j => ?_
    push_cast; rw [add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h
end GlobalTheory.TorusElliptic
