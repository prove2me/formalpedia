-- Prove2me | solution 1 for GlobalTheory.continuousOn_matrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:49.332918+00:00
-- url     : https://prove2.me/submissions/6111a007-917c-45b6-aaf7-5aaac3857af0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
namespace GlobalTheory
theorem _root_.solution {A : X → Matrix n n ℂ} (hA : ContinuousOn A U)
    (hu : ∀ x ∈ U, IsUnit (A x)) : ContinuousOn (fun x => (A x)⁻¹) U := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((continuous_id.matrix_det.comp_continuousOn hA).inv₀ fun x hx =>
    ((isUnit_iff_isUnit_det _).1 (hu x hx)).ne_zero).smul
    (continuous_id.matrix_adjugate.comp_continuousOn hA)
end GlobalTheory
