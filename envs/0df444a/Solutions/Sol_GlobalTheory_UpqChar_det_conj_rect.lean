-- Prove2me | solution 1 for GlobalTheory.UpqChar.det_conj_rect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:32.355127+00:00
-- url     : https://prove2.me/submissions/eb6db086-dec8-46c0-900f-1120205ae84c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryPQContinuousCharacterEqDetPowProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UpqChar
namespace GlobalTheory.UpqChar
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (B' : Matrix κ ι ℂ) (h1 : B * B' = 1) (h2 : B' * B = 1)
    (M : Matrix κ κ ℂ) : (B * M * B').det = M.det := by
  classical
  have hcard : Fintype.card κ = Fintype.card ι := by
    let e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
      { toFun := fun v => B *ᵥ v
        invFun := fun v => B' *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add B v w
        map_smul' := fun a v => by simp [Matrix.mulVec_smul]
        left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2]
        right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    simpa using e.finrank_eq
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hC : B.submatrix id e * B'.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_id_id]
  have hM : B * M * B' = B.submatrix id e * M.submatrix e e * B'.submatrix e id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hd : (B.submatrix id e).det * (B'.submatrix e id).det = 1 := by
    rw [← Matrix.det_mul, hC, Matrix.det_one]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  calc (B.submatrix id e).det * M.det * (B'.submatrix e id).det
      = ((B.submatrix id e).det * (B'.submatrix e id).det) * M.det := by ring
    _ = M.det := by rw [hd, one_mul]
end GlobalTheory.UpqChar
