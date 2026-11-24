-- Prove2me | solution 1 for GlobalTheory.HermWitt.congr_of_fromBlocks_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:11:32.334883+00:00
-- url     : https://prove2.me/submissions/589ebcde-10d0-4b91-bc3e-61ae00cfbe78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq_of_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {m : Type*} [Fintype m] [DecidableEq m] {D : Matrix m m E} (hD : ∀ a b, c (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, c (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map c) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map c := by
  have hH : ∀ a b, c (fromBlocks D 0 0 G₁ a b) = fromBlocks D 0 0 G₁ b a := by
    rintro (a | a) (b | b) <;> simp [hD, hG]
  let J : Matrix (m ⊕ n) m E := fromRows 1 0
  have hJ : ∀ G : Matrix n n E, Jᵀ * fromBlocks D 0 0 G * J.map c = D := by
    intro G
    have : J.map c = J := by
      ext (a | a) b <;> simp [J, Matrix.one_apply]
    rw [this]
    simp [J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have hPJ : (P * J)ᵀ * fromBlocks D 0 0 G₁ * (P * J).map c = D := by
    rw [← hJ G₂]
    conv_rhs => rw [h]
    rw [hJ G₂, transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨γ, hγ, e⟩ := exists_gl_isometry_mul_eq_of_det_ne_zero h2 hc hH (X := P * J) (Y := J)
    (by rwa [hPJ]) (by rw [hPJ, hJ])
  have hQ : fromBlocks D 0 0 G₂ = ((γ : Matrix _ _ E) * P)ᵀ * fromBlocks D 0 0 G₁ *
      ((γ : Matrix _ _ E) * P).map c := by
    rw [h]
    conv_lhs => rw [← hγ]
    rw [transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hQd : ((γ : Matrix _ _ E) * P).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero γ) hP
  rw [← Matrix.mul_assoc] at e
  generalize (γ : Matrix _ _ E) * P = Q at hQ hQd e
  obtain ⟨A, B, C, F, rfl⟩ : ∃ A B C F, Q = fromBlocks A B C F :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Q).symm⟩
  have e' : A = 1 ∧ C = 0 := by
    simpa [J, fromBlocks_mul_fromRows, fromRows_ext_iff] using e
  obtain ⟨rfl, rfl⟩ := e'
  rw [det_fromBlocks_zero₂₁, det_one, one_mul] at hQd
  rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hQ
  obtain ⟨-, h12, -, h22⟩ := hQ
  have hB : D * B.map c = 0 := by simpa using h12.symm
  refine ⟨F, hQd, ?_⟩
  rw [h22]
  simp [Matrix.mul_assoc, hB]
end GlobalTheory.HermWitt
