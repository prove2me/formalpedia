-- Prove2me | solution 1 for GlobalTheory.LatExpSum.summable_exp_neg_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:45.31595+00:00
-- url     : https://prove2.me/submissions/674430ec-6fb0-4419-9e26-20ebc27b22ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.LatExpSum
namespace GlobalTheory.LatExpSum
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : Summable fun n : ℤ => Real.exp (-ε * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf
end GlobalTheory.LatExpSum
