-- Prove2me | solution 1 for GlobalTheory.liftsToSymplectic_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:05.641744+00:00
-- url     : https://prove2.me/submissions/62b65c82-7995-461f-9d0e-c27a2b3aa232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_upper
import Theorems.Thm_GlobalTheory_LiftsToDetOne_lower
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_upper
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_lower
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_levi
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
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {l : Type*} [Fintype l] [DecidableEq l]
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)] (hf : Surjective f)
    {A B C D : Matrix l l R} (h : fromBlocks A B C D ∈ symplecticGroup l R) (hA : IsUnit A.det) :
    LiftsToSymplectic f (fromBlocks A B C D) := by
  have := A.invertibleOfIsUnitDet hA
  obtain ⟨h₁, h₂, h₃⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  obtain ⟨h₄, -, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1
    (fromBlocks_transpose A B C D ▸ SymplecticGroup.transpose_mem h)
  simp only [transpose_transpose] at h₄
  have hC : (C * A⁻¹).IsSymm := by
    have : Cᵀ = Aᵀ * C * A⁻¹ := by rw [h₁, mul_inv_cancel_right_of_invertible]
    rw [Matrix.IsSymm, transpose_mul, this, transpose_nonsing_inv, Matrix.mul_assoc,
      inv_mul_cancel_left_of_invertible]
  have hB : (A⁻¹ * B).IsSymm := by
    have : Bᵀ = A⁻¹ * (B * Aᵀ) := by rw [← h₄, inv_mul_cancel_left_of_invertible]
    rw [Matrix.IsSymm, transpose_mul, this, transpose_nonsing_inv, ← Matrix.mul_assoc,
      mul_inv_cancel_right_of_invertible]
  have hD : Aᵀ * (D - C * A⁻¹ * B) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁,
      mul_inv_cancel_right_of_invertible, h₃]
  have := ((LiftsToSymplectic.lower hf hC).mul (LiftsToSymplectic.levi hf hD)).mul
    (LiftsToSymplectic.upper hf hB)
  simpa [fromBlocks_multiply, Matrix.mul_assoc] using this
end GlobalTheory
