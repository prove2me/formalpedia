-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.isSymplecticFamily_iff_toMatrix_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:04.411102+00:00
-- url     : https://prove2.me/submissions/3f3bb312-ee96-4d2c-8225-440379c9418b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_isSymplecticFamily_iff_gram
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_toMatrix_eq
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_toMatrix_eq
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
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      b.toMatrix v ∈ symplecticGroup l R := by
  have h : (Matrix.of fun i j => B (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J l R) * b.toMatrix v := by
    ext i j
    rw [← hb.toMatrix_eq hB, of_apply]
    conv_lhs => rw [← b.sum_toMatrix_smul_self v i, ← b.sum_toMatrix_smul_self v j]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mul_apply, transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [isSymplecticFamily_iff_gram hB, h, SymplecticGroup.mem_iff', Matrix.mul_neg, Matrix.neg_mul,
    neg_inj]
end IsSymplecticBasis
end GlobalTheory
