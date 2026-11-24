-- Prove2me | solution 1 for GlobalTheory.det_fromBlocks_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:45.826332+00:00
-- url     : https://prove2.me/submissions/82a9af23-3ef7-40d8-9216-4c87bd2437f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Theorems.Thm_GlobalTheory_det_updateRow_last_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then a else 0)
      (Matrix.diagonal fun i => if i = Fin.last r then b else 0) W).det
      = Z.det * W.det - a * b * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  set l := Fin.last r with hl
  set D : K → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun c => Matrix.diagonal fun i => if i = l then c else 0 with hD
  have h1 : Matrix.fromBlocks Z (D a) (D b) W
      = (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l)
          (Matrix.fromBlocks Z 0 (D b) W (Sum.inl l) + a • Pi.single (Sum.inr l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h2 : (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l) (Pi.single (Sum.inr l) 1)
      = (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
          (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W (Sum.inr l)
            + b • Pi.single (Sum.inl l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h3 : (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1)
      = (Matrix.fromBlocks (Z.updateRow l (Pi.single l 1)) 0 0
          (W.updateRow l (Pi.single l 1))).submatrix (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm,
        Equiv.swap_apply_def] <;> grind
  have h0 : (Z.updateRow l 0).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  change (Matrix.fromBlocks Z (D a) (D b) W).det = _
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h2,
    Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h3,
    Matrix.det_permute, Equiv.Perm.sign_swap (by simp), Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h0, hl,
    det_updateRow_last_single, det_updateRow_last_single]
  simp
  ring
end GlobalTheory
