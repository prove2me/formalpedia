-- Prove2me | solution 1 for GlobalTheory.IsSiegel.transpose_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.31541+00:00
-- url     : https://prove2.me/submissions/7b0ae398-d2f0-48d8-8957-fc4f3ecfa479

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
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) {P : Matrix ι ι ℝ}
    (hP : P.det ≠ 0) : IsSiegel ((P.map ofReal)ᵀ * σ * P.map ofReal) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isSymm.eq,
      Matrix.mul_assoc]
  · convert h.posDef.conjTranspose_mul_mul_same (B := P)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det P).2 hP.isUnit)) using 1
    ext i j
    simp [mul_apply]
end IsSiegel
end GlobalTheory
