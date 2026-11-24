-- Prove2me | solution 1 for GlobalTheory.IsSiegel.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:19.175469+00:00
-- url     : https://prove2.me/submissions/3d2470c6-4570-4feb-8e2a-8e5385e0be37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eq_transpose_mul_diagonal_mul
import Theorems.Thm_GlobalTheory_isUnit_det_map_ofReal

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
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) : IsUnit σ.det := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  rw [det_mul, det_mul, det_transpose, det_diagonal]
  refine ((isUnit_det_map_ofReal hP).mul (IsUnit.mk0 _ ?_)).mul (isUnit_det_map_ofReal hP)
  exact Finset.prod_ne_zero_iff.2 fun i _ h0 => by simpa [h0] using ht i
end IsSiegel
end GlobalTheory
