-- Prove2me | solution 1 for GlobalTheory.specialLinearGroup_map_zmod_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:15.221799+00:00
-- url     : https://prove2.me/submissions/2055394b-31be-4434-b8c7-0577a757c880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_specialLinearGroup_map_surjective
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] (N : ℕ) :
    Surjective (SpecialLinearGroup.map (n := n) (Int.castRingHom (ZMod N))) := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact fun A => ⟨A, Subtype.ext (Matrix.ext fun _ _ => rfl)⟩
  · have : NeZero N := ⟨hN⟩
    exact specialLinearGroup_map_surjective (ZMod.ringHom_surjective _)
end GlobalTheory
