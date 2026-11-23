-- Prove2me | solution 1 for GlobalTheory.LLeft.summable_nine_pow_mul_inv_sq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.40005+00:00
-- url     : https://prove2.me/submissions/200e1bb6-bfda-4695-9b74-225c6495b6ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (t : ℝ) (ht : 1 < t) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-t)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
    (show -t < -1 by linarith))
  simpa using this
end GlobalTheory.LLeft
