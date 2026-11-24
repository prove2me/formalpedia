-- Prove2me | solution 1 for GlobalTheory.isUnit_det_map_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:48.376502+00:00
-- url     : https://prove2.me/submissions/f3c94595-08bb-41dd-bd41-e717699e2fea

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
    IsUnit (P.map ofReal).det := by
  have : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
  rw [this]
  simpa using hP
end GlobalTheory
