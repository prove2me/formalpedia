-- Prove2me | solution 1 for GlobalTheory.IsSiegel.siegelGaussIntegral_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:49.965563+00:00
-- url     : https://prove2.me/submissions/a1c3090a-66b5-4fb8-8ebf-21ebacbbcbb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_sq_mul_det

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
    siegelGaussIntegral σ ≠ 0 := fun h0 => by
  simpa [h0] using h.siegelGaussIntegral_sq_mul_det
end IsSiegel
end GlobalTheory
