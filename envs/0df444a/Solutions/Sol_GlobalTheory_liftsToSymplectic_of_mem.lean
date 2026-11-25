-- Prove2me | solution 1 for GlobalTheory.liftsToSymplectic_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:00.03849+00:00
-- url     : https://prove2.me/submissions/95ec8d67-8ee1-447a-95cb-9ae245f5aaee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_upper
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_upper
import Theorems.Thm_GlobalTheory_exists_isSymm_isUnit_add_mul
import Theorems.Thm_GlobalTheory_liftsToSymplectic_of_isUnit
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
    {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) : LiftsToSymplectic f M := by
  rw [← M.fromBlocks_toBlocks] at hM ⊢
  obtain ⟨X, hX, hu⟩ := exists_isSymm_isUnit_add_mul hM
  have hmem : fromBlocks 1 X 0 1 ∈ symplecticGroup l R := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have h := mul_mem hmem hM
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add] at h
  have := (LiftsToSymplectic.upper hf hX.neg).mul (liftsToSymplectic_of_isUnit hf h hu)
  simpa only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add, Matrix.neg_mul,
    add_neg_cancel_right] using this
end GlobalTheory
