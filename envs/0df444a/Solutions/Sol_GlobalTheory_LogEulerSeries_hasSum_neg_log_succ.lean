-- Prove2me | solution 1 for GlobalTheory.LogEulerSeries.hasSum_neg_log_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:19.118963+00:00
-- url     : https://prove2.me/submissions/88b21ac9-1714-474c-8e37-71fd294b57fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.LogEulerSeries
namespace GlobalTheory.LogEulerSeries
theorem _root_.solution {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa using h2
end GlobalTheory.LogEulerSeries
