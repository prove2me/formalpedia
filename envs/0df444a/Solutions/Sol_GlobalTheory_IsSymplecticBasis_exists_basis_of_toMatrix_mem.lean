-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.exists_basis_of_toMatrix_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:10.423803+00:00
-- url     : https://prove2.me/submissions/fb621db9-6c3e-4f75-b606-2cfff0c8d75a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_isSymplecticFamily_iff_toMatrix_mem
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
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) {v : l ⊕ l → M}
    (hv : b.toMatrix v ∈ symplecticGroup l R) :
    ∃ c : Basis (l ⊕ l) R M, IsSymplecticBasis B c ∧ ⇑c = v := by
  obtain ⟨h₁, h₂⟩ := (b.is_basis_iff_det (v := v)).2 (SymplecticGroup.symplectic_det hv)
  refine ⟨Basis.mk h₁ h₂.ge, ?_, Basis.coe_mk _ _⟩
  simpa [IsSymplecticBasis, IsSymplecticBasisOfType] using
    (hb.isSymplecticFamily_iff_toMatrix_mem hB v).2 hv
end IsSymplecticBasis
end GlobalTheory
