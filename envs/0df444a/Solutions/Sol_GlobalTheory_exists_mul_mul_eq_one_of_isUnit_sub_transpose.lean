-- Prove2me | solution 1 for GlobalTheory.exists_mul_mul_eq_one_of_isUnit_sub_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:20.414288+00:00
-- url     : https://prove2.me/submissions/c0d0d70d-3180-4029-9710-6db1e5403c92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_isUnit_of_forall_maximalSpectrum_mk_ne_zero
import Theorems.Thm_GlobalTheory_exists_matrix_lift_maximalSpectrum
import Theorems.Thm_GlobalTheory_exists_mul_mul_eq_one_of_card_le_rank
import Theorems.Thm_GlobalTheory_matrix_rank_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)]
    {G : Matrix (l ⊕ l) (l ⊕ l) R} (h : IsUnit (G - Gᵀ).det) :
    ∃ (U : Matrix l (l ⊕ l) R) (V : Matrix (l ⊕ l) l R), U * G * V = 1 := by
  have key : ∀ p : MaximalSpectrum R, ∃ (U : Matrix l (l ⊕ l) (R ⧸ p.asIdeal))
      (V : Matrix (l ⊕ l) l (R ⧸ p.asIdeal)), U * G.map (Ideal.Quotient.mk p.asIdeal) * V = 1 := by
    intro p
    have := p.isMaximal
    let _ := Ideal.Quotient.field p.asIdeal
    refine exists_mul_mul_eq_one_of_card_le_rank _ ?_
    have h₁ := h.map (Ideal.Quotient.mk p.asIdeal)
    rw [RingHom.map_det, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      transpose_map, ← isUnit_iff_isUnit_det] at h₁
    have h₂ := matrix_rank_sub_le (G.map (Ideal.Quotient.mk p.asIdeal))
      (G.map (Ideal.Quotient.mk p.asIdeal))ᵀ
    rw [rank_of_isUnit _ h₁, rank_transpose, Fintype.card_sum] at h₂
    omega
  choose U V hUV using key
  obtain ⟨U', hU⟩ := exists_matrix_lift_maximalSpectrum U
  obtain ⟨V', hV⟩ := exists_matrix_lift_maximalSpectrum V
  have hu : IsUnit (U' * G * V').det := isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => by
    have := p.isMaximal
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, hU, hV, hUV,
      det_one]
    exact one_ne_zero
  exact ⟨U', V' * (U' * G * V')⁻¹, by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu]⟩
end GlobalTheory
