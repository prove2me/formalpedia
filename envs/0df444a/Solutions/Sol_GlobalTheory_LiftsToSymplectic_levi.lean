-- Prove2me | solution 1 for GlobalTheory.LiftsToSymplectic.levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:30.213803+00:00
-- url     : https://prove2.me/submissions/6414724e-d052-4d8b-8ba2-90b2f0009895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_levi_of_isSymm
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_levi_of_det_eq_one
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
    (h : Xᵀ * Y = 1) : LiftsToSymplectic f (fromBlocks X 0 0 Y) := by
  rcases isEmpty_or_nonempty l with hl | ⟨⟨i⟩⟩
  · exact levi_of_det_eq_one hf det_isEmpty h
  have hd : X.det * Y.det = 1 := by simpa using congrArg det h
  let D : Matrix l l R := diagonal (Function.update 1 i X.det)
  let E : Matrix l l R := diagonal (Function.update 1 i Y.det)
  have hDE : D * E = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i
    · simp [hj, hd]
    · simp [hj]
  have hED : E * D = 1 := mul_eq_one_comm.1 hDE
  have h₁ := levi_of_isSymm hf (isSymm_diagonal _) (isSymm_diagonal _) hDE
  have h₂ : LiftsToSymplectic f (fromBlocks (E * X) 0 0 (D * Y)) := by
    refine levi_of_det_eq_one hf ?_ ?_
    · rw [det_mul, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp [mul_comm, hd]
    · rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc _ D, hED,
        Matrix.one_mul, h]
  have := h₁.mul h₂
  rw [fromBlocks_multiply] at this
  simpa [← Matrix.mul_assoc, D, E, hDE, hED, -diagonal_mul_diagonal] using this
end GlobalTheory.LiftsToSymplectic
