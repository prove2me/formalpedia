-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.form_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:09.494427+00:00
-- url     : https://prove2.me/submissions/c8fc2349-d241-4125-bedd-d776a56f25d2

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
    (i j : Fin g) :
    (Pi.single i 1 : Fin g → ℂ) ⬝ᵥ Y *ᵥ star (Pi.single j 1 : Fin g → ℂ) = Y i j := by
  simp [Pi.star_single]
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
