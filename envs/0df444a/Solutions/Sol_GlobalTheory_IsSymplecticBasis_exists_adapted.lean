-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.exists_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:33.604415+00:00
-- url     : https://prove2.me/submissions/217b45e1-5f02-4474-8c26-6a65743ed3b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_exists_mul_mul_eq_one_of_isUnit_sub_transpose
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_isSymplecticFamily_iff_toMatrix_mem
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_basis_of_toMatrix_mem
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
omit [DecidableEq l]
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution [Finite (MaximalSpectrum R)] {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) {P Q : Submodule R M}
    (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) R M, IsSymplecticBasis B c ∧ (∀ i, c (.inl i) ∈ P) ∧
      ∀ i, c (.inr i) ∈ Q := by
  classical
  have : ∀ i, ∃ p ∈ P, ∃ q ∈ Q, p + q = b i := fun i =>
    Submodule.mem_sup.1 (hPQ ▸ Submodule.mem_top)
  choose p hp q hq hpq using this
  let G : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.of fun i j => B (p i) (q j)
  have hG : G - Gᵀ = -Matrix.J l R := by
    rw [← hb.toMatrix_eq hB]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, ← hpq, ← hpq]
    simp [G, hP _ (hp i) _ (hp j), hQ _ (hq i) _ (hq j), ← hB.neg_eq (p j), sub_eq_add_neg,
      add_comm]
  obtain ⟨U, V, hUV⟩ := exists_mul_mul_eq_one_of_isUnit_sub_transpose (G := G)
    (hG ▸ SymplecticGroup.symplectic_det (SymplecticGroup.neg_mem (SymplecticGroup.J_mem l R)))
  let x : l → M := fun i => ∑ k, U i k • p k
  let y : l → M := fun j => ∑ k, V k j • q k
  have hx : ∀ i, x i ∈ P := fun i => P.sum_mem fun k _ => P.smul_mem _ (hp k)
  have hy : ∀ i, y i ∈ Q := fun i => Q.sum_mem fun k _ => Q.smul_mem _ (hq k)
  have hxy : ∀ i j, B (x i) (y j) = (1 : Matrix l l R) i j := fun i j => by
    rw [← hUV]
    simp only [x, y, G, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mul_apply, of_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hB
    ((hb.isSymplecticFamily_iff_toMatrix_mem hB (Sum.elim x y)).1
      ⟨fun i j => hP _ (hx i) _ (hx j), fun i j => hQ _ (hy i) _ (hy j),
        fun i => by simp [hxy], fun i j hij => by simp [hxy, hij]⟩)
  exact ⟨c, hc, fun i => hcv ▸ hx i, fun i => hcv ▸ hy i⟩
end IsSymplecticBasis
end GlobalTheory
