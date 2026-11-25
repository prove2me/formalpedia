-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:49.196108+00:00
-- url     : https://prove2.me/submissions/edb440b2-67cd-41a4-9aed-6d03b898368d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_liftsToSymplectic_of_mem
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_toMatrix_mem
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_basis_of_toMatrix_mem
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
variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution (hf : Surjective f) (hB : B.IsAlt) (hB' : B'.IsAlt)
    (φ : Λ →ₛₗ[f] M) {b : Basis (l ⊕ l) S Λ} {b' : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hb' : IsSymplecticBasis B' b') (h : ∀ i, φ (b i) = b' i)
    {c' : Basis (l ⊕ l) R M} (hc' : IsSymplecticBasis B' c') :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧ ∀ i, φ (c i) = c' i := by
  classical
  obtain ⟨T, hT, hT'⟩ := liftsToSymplectic_of_mem hf (hb'.toMatrix_mem hc' hB')
  have hv : b.toMatrix (fun j => ∑ k, T k j • b k) = T := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hB (hv.symm ▸ hT)
  refine ⟨c, hc, fun j => ?_⟩
  rw [hcv, ← b'.sum_toMatrix_smul_self c' j, ← hT']
  simp only [map_sum φ, φ.map_smulₛₗ, h, map_apply]
end IsSymplecticBasis
end GlobalTheory
