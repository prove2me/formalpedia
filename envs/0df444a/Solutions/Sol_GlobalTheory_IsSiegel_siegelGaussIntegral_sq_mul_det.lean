-- Prove2me | solution 1 for GlobalTheory.IsSiegel.siegelGaussIntegral_sq_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:30.853808+00:00
-- url     : https://prove2.me/submissions/c295efcb-8f3d-4277-8682-ef7b2d263906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_exists_integral_cexp_quadratic
import Theorems.Thm_GlobalTheory_IsSiegel_integral_cexp_quadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    siegelGaussIntegral σ ^ 2 * (-I • σ).det = 1 := by
  obtain ⟨s, hs1, hs⟩ := h.exists_integral_cexp_quadratic
  have h0 := (h.integral_cexp_quadratic 0).symm.trans (hs 0)
  rw [mul_left_inj' (Complex.exp_ne_zero _)] at h0
  rwa [h0]
end IsSiegel
end GlobalTheory
