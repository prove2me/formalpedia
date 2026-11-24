-- Prove2me | solution 1 for GlobalTheory.LiftsToSymplectic.levi_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:44.526037+00:00
-- url     : https://prove2.me/submissions/36226b66-584b-4613-80a0-9a43368db819

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_adjugate
import Theorems.Thm_GlobalTheory_liftsToDetOne_of_det_eq_one
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
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
open GlobalTheory.LiftsToSymplectic
namespace GlobalTheory.LiftsToSymplectic
theorem _root_.solution [Finite (MaximalSpectrum R)] (hf : Surjective f) {X Y : Matrix l l R}
    (hX : X.det = 1) (h : Xᵀ * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  obtain ⟨A, hA, rfl⟩ := liftsToDetOne_of_det_eq_one hf hX
  have hA' : Aᵀ * Aᵀ.adjugate = 1 := by simp [mul_adjugate, hA]
  refine ⟨fromBlocks A 0 0 Aᵀ.adjugate, by simp [SymplecticGroup.fromBlocks_mem_iff, hA'], ?_⟩
  have : Aᵀ.adjugate.map f = Y := by
    refine right_inv_eq_right_inv ?_ h
    rw [← transpose_map, ← Matrix.map_mul, hA']
    simp
  simp [fromBlocks_map, this]
end GlobalTheory.LiftsToSymplectic
