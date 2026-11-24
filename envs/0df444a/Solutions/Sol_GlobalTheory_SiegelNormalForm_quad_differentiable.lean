-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.quad_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.20605+00:00
-- url     : https://prove2.me/submissions/bb9ae745-ed41-449d-b96a-32d513b1e64d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.SiegelNormalForm
namespace _root_.GlobalTheory.SiegelNormalForm
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℂ)
    (c : Fin g → ℂ) : Differentiable ℂ (_root_.GlobalTheory.SiegelNormalForm.quad Y c) := by
  unfold _root_.GlobalTheory.SiegelNormalForm.quad
  simp only [dotProduct, mulVec]
  fun_prop
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
