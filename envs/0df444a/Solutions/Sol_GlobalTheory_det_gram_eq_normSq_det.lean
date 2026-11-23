-- Prove2me | solution 1 for GlobalTheory.det_gram_eq_normSq_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:02.969913+00:00
-- url     : https://prove2.me/submissions/49cea627-2388-468b-bd65-cb550ad36869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by
  have h : b.toBasis.det v = (Matrix.of fun i j ↦ b.repr (v j) i).det := by
    rw [Basis.det_apply]; congr 1
  rw [gram_eq_conjTranspose_mul b v, det_mul, det_conjTranspose, h, RCLike.star_def,
    RCLike.conj_mul]
  push_cast; rfl
end GlobalTheory
