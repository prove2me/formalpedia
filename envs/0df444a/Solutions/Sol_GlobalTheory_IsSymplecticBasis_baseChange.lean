-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:25.357986+00:00
-- url     : https://prove2.me/submissions/a7d433cd-529d-402c-8287-17e2ab9b687e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
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
variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}
omit [Fintype l]
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution [Algebra S R] {b : Basis (l ⊕ l) S Λ}
    (hb : IsSymplecticBasis B b) : IsSymplecticBasis (B.baseChange R) (b.baseChange R) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp [hb.left_left]
  · simp [hb.right_right]
  · simp [IsSymplecticFamily.left_right_self hb i]
  · simp [IsSymplecticFamily.left_right_ne hb i j hij]
end IsSymplecticBasis
end GlobalTheory
