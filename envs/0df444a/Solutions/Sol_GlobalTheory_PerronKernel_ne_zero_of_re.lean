-- Prove2me | solution 1 for GlobalTheory.PerronKernel.ne_zero_of_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:09.250961+00:00
-- url     : https://prove2.me/submissions/88aae394-4cf3-4364-96c0-3c2a700d24fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution {σ t : ℝ} (h : σ ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by
  intro h0
  apply h
  simpa using congrArg Complex.re h0
end GlobalTheory.PerronKernel
