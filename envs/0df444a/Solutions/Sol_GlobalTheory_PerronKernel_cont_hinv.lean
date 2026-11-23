-- Prove2me | solution 1 for GlobalTheory.PerronKernel.cont_hinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:04.335095+00:00
-- url     : https://prove2.me/submissions/73045924-d3cc-4986-a5e1-6b847e865d73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_im

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
theorem _root_.solution {t : ℝ} (h : t ≠ 0) : Continuous fun σ : ℝ => ((σ : ℂ) + t * I)⁻¹ := by
  exact (by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + t * I).inv₀ fun σ => ne_zero_of_im h
end GlobalTheory.PerronKernel
