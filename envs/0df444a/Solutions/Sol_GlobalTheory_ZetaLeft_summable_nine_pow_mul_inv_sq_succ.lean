-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.summable_nine_pow_mul_inv_sq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:11.919544+00:00
-- url     : https://prove2.me/submissions/b9094b12-1672-4afe-8c2b-910caf410f39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(9/8 : ℝ) < -1))
  simpa using this
end GlobalTheory.ZetaLeft
