-- Prove2me | solution 1 for GlobalTheory.ofReal_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:42.453077+00:00
-- url     : https://prove2.me/submissions/aa035a61-a2d9-4f96-9236-7d8248c2cd11

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
omit [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    (fun i => ((P *ᵥ x) i : ℂ)) = P.map ofReal *ᵥ fun i => (x i : ℂ) := by
  ext i
  simp [mulVec, dotProduct]
end GlobalTheory
