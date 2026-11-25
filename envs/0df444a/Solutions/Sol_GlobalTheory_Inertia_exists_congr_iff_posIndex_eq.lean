-- Prove2me | solution 1 for GlobalTheory.Inertia.exists_congr_iff_posIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:48.617259+00:00
-- url     : https://prove2.me/submissions/bd5341db-6dfe-4a0b-b491-3fe6243676fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_congr_mul
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_real
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_of_card_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution {G H : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (hH : H.IsHermitian) (hH0 : H.det ≠ 0) :
    (∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = H) ↔ posIndex G = posIndex H := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (posIndex_congr G hP).symm
  · intro h
    obtain ⟨Q, d, hQ, hd, hne⟩ := exists_congr_diagonal_real hH
    obtain ⟨P, hP, hPd⟩ := exists_congr_diagonal_of_card_eq hG hG0 (hne hH0) (by
      rw [h, posIndex_eq_card_of_congr_diagonal hQ hd]
      simp)
    have hu : IsUnit Q.det := hQ.isUnit
    refine ⟨P * Q⁻¹, ?_, ?_⟩
    · rw [det_mul]
      exact mul_ne_zero hP (isUnit_nonsing_inv_det Q hu).ne_zero
    · rw [congr_mul, hPd, ← hd, ← congr_mul, mul_nonsing_inv Q hu]
      simp
end GlobalTheory.Inertia
