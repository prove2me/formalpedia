-- Prove2me | solution 1 for GlobalTheory.inv_map_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.21587+00:00
-- url     : https://prove2.me/submissions/eb26a870-2acc-47cc-98a3-0f5cb02e6401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul

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
theorem _root_.solution {P : Matrix ι ι ℝ} (hP : P.det ≠ 0) :
    (P.map ofReal)⁻¹ = P⁻¹.map ofReal := by
  refine inv_eq_right_inv ?_
  change P.map ofRealHom * P⁻¹.map ofRealHom = 1
  rw [← Matrix.map_mul, mul_nonsing_inv _ hP.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
end GlobalTheory
