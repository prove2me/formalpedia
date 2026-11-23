-- Prove2me | solution 1 for GlobalTheory.PerronKernel.norm_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:05.052309+00:00
-- url     : https://prove2.me/submissions/83c5ffa0-d169-46d3-9b7a-d90f0ab9fbc7

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
theorem _root_.solution (L σ t : ℝ) : ‖cexp (L * ((σ : ℂ) + t * I))‖ = Real.exp (L * σ) := by
  rw [Complex.norm_exp]
  simp
end GlobalTheory.PerronKernel
