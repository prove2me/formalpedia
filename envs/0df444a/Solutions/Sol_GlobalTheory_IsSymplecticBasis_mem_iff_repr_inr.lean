-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.mem_iff_repr_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:19.138231+00:00
-- url     : https://prove2.me/submissions/82fd5fb7-afd8-46d3-9a7d-af85168b6cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_left
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
omit [DecidableEq l]
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {P : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (h : ∀ i, b (.inl i) ∈ P) (x : M) :
    x ∈ P ↔ ∀ i, b.repr x (.inr i) = 0 := by
  refine ⟨fun hx i => by rw [← hb.apply_left, hP _ (h i) _ hx], fun hx => ?_⟩
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [hx] using P.sum_mem fun i _ => P.smul_mem _ (h i)
end IsSymplecticBasis
end GlobalTheory
