-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.span_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:19.777797+00:00
-- url     : https://prove2.me/submissions/722dd67b-ed0f-4b12-b12c-539a7e039187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_iff_repr_inr
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
    {P : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (h : ∀ i, b (.inl i) ∈ P) :
    Submodule.span R (Set.range fun i => b (.inl i)) = P := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 h)) fun x hx => ?_
  rw [← b.sum_repr x, Fintype.sum_sum_type]
  simpa [(hb.mem_iff_repr_inr hP h x).1 hx] using
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
end IsSymplecticBasis
end GlobalTheory
