-- Prove2me | solution 1 for GlobalTheory.Hk.summable_nat_mul_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:04.466359+00:00
-- url     : https://prove2.me/submissions/4f2f7d1a-aece-4f1c-8bb0-2e58b4485b84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(t * n))) := by
  have := Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  simpa using this
end GlobalTheory.Hk
