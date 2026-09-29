-- Prove2me | solution 1 for Matrix.charpoly_of_uString
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/037789d6-99af-514b-b7ff-ce1c27a51fbd

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_charpoly_of_uString

set_option autoImplicit false

open Polynomial

namespace Matrix p2m_export "Matrix" "J det_succ_row charmatrix ext row zero det_fin_one submatrix_apply charpoly det_fin_two charmatrix_apply_eq det diagonal of submatrix charmatrix_apply_ne" end Matrix
p2m_open_scoped "Matrix" in

def Matrix.uString (F : Type) [Field F] (e : ℕ) (a b : F) : Matrix (Fin (e + 1)) (Fin (e + 1)) F :=
  Matrix.of fun i j => if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
    else (if (i : ℕ) + 1 = (j : ℕ) then 1 else 0)

namespace Matrix
p2m_export "Matrix" "J det_succ_row charmatrix ext row zero det_fin_one submatrix_apply charpoly det_fin_two charmatrix_apply_eq det diagonal of submatrix charmatrix_apply_ne"
namespace UStringAux
p2m_open "Matrix"

variable (F : Type) [Field F]

theorem uString_apply (e : ℕ) (a b : F) (i j : Fin (e + 1)) :
    Matrix.uString F e a b i j =
      if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
      else (if (i : ℕ) + 1 = (j : ℕ) then 1 else 0) := rfl

theorem charmatrix_uString_submatrix_castSucc (e : ℕ) (a b : F) :
    (Matrix.uString F (e + 1) a b).charmatrix.submatrix Fin.castSucc Fin.castSucc =
      (Matrix.uString F e a b).charmatrix := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    rw [Matrix.submatrix_apply, Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq, uString_apply,
      uString_apply, Fin.val_castSucc]
  · rw [Matrix.submatrix_apply, Matrix.charmatrix_apply_ne _ _ _ (fun hh => h (Fin.castSucc_injective _ hh)),
      Matrix.charmatrix_apply_ne _ _ _ h, uString_apply, uString_apply, Fin.val_castSucc, Fin.val_castSucc]

theorem charmatrix_uString_last_of_ne (e : ℕ) (a b : F) (j : Fin (e + 2 + 1))
    (hj : j ≠ Fin.last (e + 2)) :
    (Matrix.uString F (e + 2) a b).charmatrix (Fin.last (e + 2)) j = 0 := by
  rw [Matrix.charmatrix_apply_ne _ _ _ (Ne.symm hj), uString_apply, Fin.val_last]
  have hj' : (j : ℕ) ≠ e + 2 := fun h => hj (Fin.ext (by rw [h, Fin.val_last]))
  have hjlt : (j : ℕ) < e + 2 + 1 := j.isLt
  by_cases hj0 : (j : ℕ) = 0
  · rw [if_pos hj0, if_neg (by omega), if_neg (by omega), map_zero, neg_zero]
  · rw [if_neg hj0, if_neg (by omega), map_zero, neg_zero]

theorem charmatrix_uString_last_last (e : ℕ) (a b : F) :
    (Matrix.uString F (e + 2) a b).charmatrix (Fin.last (e + 2)) (Fin.last (e + 2)) = X := by
  rw [Matrix.charmatrix_apply_eq, uString_apply, Fin.val_last, if_neg (by omega), if_neg (by omega), map_zero,
    sub_zero]

theorem charpoly_uString_succ_succ (e : ℕ) (a b : F) :
    (Matrix.uString F (e + 2) a b).charpoly = X * (Matrix.uString F (e + 1) a b).charpoly := by
  rw [Matrix.charpoly, Matrix.det_succ_row _ (Fin.last (e + 2)), Finset.sum_eq_single (Fin.last (e + 2))]
  · rw [Fin.succAbove_last, charmatrix_uString_last_last, charmatrix_uString_submatrix_castSucc,
      Matrix.charpoly]
    have : ((-1 : (F)[X]) ^ ((Fin.last (e + 2) : ℕ) + (Fin.last (e + 2) : ℕ))) = 1 :=
      Even.neg_one_pow ⟨_, rfl⟩
    rw [this, one_mul]
  · intro j _ hj
    rw [charmatrix_uString_last_of_ne F e a b j hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem charpoly_uString_zero (a b : F) : (Matrix.uString F 0 a b).charpoly = X - C a := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq, uString_apply]
  simp

theorem charpoly_uString_one (a b : F) :
    (Matrix.uString F 1 a b).charpoly = X ^ 2 - C a * X + C b := by
  rw [Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne _ 0 1 (by decide), Matrix.charmatrix_apply_ne _ 1 0 (by decide),
    uString_apply, uString_apply, uString_apply, uString_apply]
  simp
  ring

theorem charpoly_uString_succ (e : ℕ) (a b : F) :
    (Matrix.uString F (e + 1) a b).charpoly = X ^ e * (X ^ 2 - C a * X + C b) := by
  induction e with
  | zero => rw [pow_zero, one_mul, charpoly_uString_one]
  | succ e ih => rw [charpoly_uString_succ_succ, ih, ← mul_assoc, ← pow_succ']

end Matrix.UStringAux

p2m_open_scoped "Matrix" in
theorem Matrix.charpoly_uString (F : Type) [Field F] (e : ℕ) (a b : F) :
    (Matrix.uString F e a b).charpoly =
      if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b) := by
  rcases e with _ | e
  · rw [if_pos rfl, Matrix.UStringAux.charpoly_uString_zero]
  · rw [if_neg (Nat.succ_ne_zero e), Matrix.UStringAux.charpoly_uString_succ, Nat.add_sub_cancel]

theorem solution (F : Type) [Field F] (e : ℕ) (a b : F) :
    (Matrix.of fun i j : Fin (e + 1) =>
        if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
        else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0)).charpoly =
      if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b) := by
  exact Matrix.charpoly_uString F e a b

end S_Matrix_charpoly_of_uString
end P2MW
export P2MW.S_Matrix_charpoly_of_uString (solution)
