-- Prove2me | solution 1 for GlobalTheory.RapidFourier.summable_inv_one_add_abs_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:40.25081+00:00
-- url     : https://prove2.me/submissions/6b8d0480-8b9c-4249-b4b1-55c53a2fadcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid

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
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution : Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
  have hN : Summable fun k : ℕ => ((1 + (k : ℝ)) ^ 2)⁻¹ := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    refine h.congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun k => ?_
    simp
  · refine hN.congr fun k => ?_
    simp
end GlobalTheory.RapidFourier
