-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.quad_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:48.783828+00:00
-- url     : https://prove2.me/submissions/a8cc7274-f142-4963-8a4f-2020c720179b

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
theorem _root_.solution {Y : Matrix (Fin g) (Fin g) ℂ} (hY : Y.IsSymm)
    (c z w : Fin g → ℂ) :
    _root_.GlobalTheory.SiegelNormalForm.quad Y c (z + w) - _root_.GlobalTheory.SiegelNormalForm.quad Y c z =
      Real.pi * (z ⬝ᵥ Y *ᵥ w) + _root_.GlobalTheory.SiegelNormalForm.quad Y c w := by
  have hwz : w ⬝ᵥ Y *ᵥ z = z ⬝ᵥ Y *ᵥ w := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hY.eq]
  simp only [_root_.GlobalTheory.SiegelNormalForm.quad, mulVec_add, dotProduct_add, add_dotProduct, hwz]
  ring
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
