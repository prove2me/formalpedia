-- Prove2me | solution 1 for GlobalTheory.PerronPsi.half_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:55.893529+00:00
-- url     : https://prove2.me/submissions/2d477f6a-4a3c-4184-89a5-7a8a66fd4d20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h1 := Real.log_two_gt_d9
  have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  linarith
end GlobalTheory.PerronPsi
