-- Prove2me | solution 1 for GlobalTheory.PerronKernel.cont_vinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:04.697015+00:00
-- url     : https://prove2.me/submissions/2f210fb9-d484-4008-8bcf-b947544929f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_re

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
theorem _root_.solution {σ : ℝ} (h : σ ≠ 0) : Continuous fun t : ℝ => ((σ : ℂ) + t * I)⁻¹ := by
  exact (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I).inv₀ fun t => ne_zero_of_re h
end GlobalTheory.PerronKernel
