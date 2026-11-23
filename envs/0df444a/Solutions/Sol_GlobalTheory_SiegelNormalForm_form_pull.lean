-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.form_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:40.162611+00:00
-- url     : https://prove2.me/submissions/0c2ff88e-9e4d-4730-b16d-c4b51584cef5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ (Pᵀ * Hm * P.map star) *ᵥ star w := by
  rw [star_mulVec, ← mulVec_transpose, conjTranspose, ← transpose_map, transpose_transpose,
    dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, mulVec_mulVec,
    mulVec_mulVec, Matrix.mul_assoc]
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
