-- Prove2me | solution 1 for GlobalTheory.isSymplecticFamily_iff_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:20.349866+00:00
-- url     : https://prove2.me/submissions/9f079e0e-d000-42b7-89f5-0d78dbc05e88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
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
variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype l] [DecidableEq l]
  {B : LinearMap.BilinForm R M}
omit [Fintype l]
namespace GlobalTheory
theorem _root_.solution (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      (Matrix.of fun i j => B (v i) (v j)) = -Matrix.J l R := by
  constructor
  · intro h
    ext (i | i) (j | j)
    · simpa [Matrix.J] using h.left_left i j
    · simpa [Matrix.J, Matrix.one_apply] using h.left_right i j
    · have := h.right_left hB i j
      simp only [of_apply, Matrix.J, Matrix.neg_apply, fromBlocks_apply₂₁, Matrix.one_apply, this]
      split_ifs <;> simp
    · simpa [Matrix.J] using h.right_right i j
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa [Matrix.J] using congrFun (congrFun h (.inl i)) (.inl j)
    · simpa [Matrix.J] using congrFun (congrFun h (.inr i)) (.inr j)
    · simpa [Matrix.J] using congrFun (congrFun h (.inl i)) (.inr i)
    · simpa [Matrix.J, hij] using congrFun (congrFun h (.inl i)) (.inr j)
end GlobalTheory
