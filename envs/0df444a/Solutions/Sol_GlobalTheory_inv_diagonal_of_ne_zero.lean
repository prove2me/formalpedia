-- Prove2me | solution 1 for GlobalTheory.inv_diagonal_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.696808+00:00
-- url     : https://prove2.me/submissions/eb4309a5-e5d9-40de-bd5f-f786adb2c6d8

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
theorem _root_.solution {t : ι → ℂ} (ht : ∀ i, t i ≠ 0) :
    (diagonal t)⁻¹ = diagonal fun i => (t i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  exact funext fun i => mul_inv_cancel₀ (ht i)
end GlobalTheory
