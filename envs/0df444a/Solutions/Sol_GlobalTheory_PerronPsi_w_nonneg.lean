-- Prove2me | solution 1 for GlobalTheory.PerronPsi.w_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:05.983272+00:00
-- url     : https://prove2.me/submissions/0b8ed4ae-4996-452e-886e-5333238fa15e

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
theorem _root_.solution (N : ℕ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ w N B n := by
  unfold w
  split_ifs <;> positivity
end GlobalTheory.PerronPsi
