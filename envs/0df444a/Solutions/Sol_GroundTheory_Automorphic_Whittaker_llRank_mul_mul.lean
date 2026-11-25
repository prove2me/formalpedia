-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.llRank_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:51.193838+00:00
-- url     : https://prove2.me/submissions/1c67bae6-7fcc-4069-9abd-0083a60009f1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rowsFrom_mul_self
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_colsTo_mul_self
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rowsFrom_mul_mul_rowsFrom
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_colsTo_mul_mul_colsTo
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isUnit_det_of_isUpperTriangular
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {b b' : GL (Fin n) F} (hb : b ∈ borel n F) (hb' : b' ∈ borel n F)
    (i j : Fin n) (g : GL (Fin n) F) : llRank i j (b * g * b') = llRank i j g := by
  classical
  have hbu : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb
  have hbu' : (b' : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb'
  set P : Matrix (Fin n) (Fin n) F := rowsFrom i with hP
  set E : Matrix (Fin n) (Fin n) F := colsTo j with hE
  set X : Matrix (Fin n) (Fin n) F := P * (b : Matrix (Fin n) (Fin n) F) + (1 - P) with hXdef
  set Y : Matrix (Fin n) (Fin n) F := (b' : Matrix (Fin n) (Fin n) F) * E + (1 - E) with hYdef
  have hXP : X * P = P * (b : Matrix (Fin n) (Fin n) F) := by
    rw [hXdef, add_mul, sub_mul, one_mul, hP, rowsFrom_mul_self, sub_self, add_zero,
      rowsFrom_mul_mul_rowsFrom hbu]
  have hEY : E * Y = (b' : Matrix (Fin n) (Fin n) F) * E := by
    rw [hYdef, mul_add, mul_sub, mul_one, hE, colsTo_mul_self, sub_self, add_zero,
      ← mul_assoc, colsTo_mul_mul_colsTo hbu']
  have key : P * ((b * g * b' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * E =
      X * (P * (g : Matrix (Fin n) (Fin n) F) * E) * Y := by
    simp only [Units.val_mul]
    calc P * ((b : Matrix (Fin n) (Fin n) F) * g * b') * E
        = (P * b) * g * (b' * E) := by simp only [mul_assoc]
      _ = (X * P) * g * (E * Y) := by rw [hXP, hEY]
      _ = X * (P * g * E) * Y := by simp only [mul_assoc]
  have hXu : X.IsUpperTriangular :=
    ((blockTriangular_diagonal _).mul hbu).add (blockTriangular_one.sub (blockTriangular_diagonal _))
  have hYu : Y.IsUpperTriangular :=
    (hbu'.mul (blockTriangular_diagonal _)).add (blockTriangular_one.sub (blockTriangular_diagonal _))
  have hX : IsUnit X.det := by
    refine isUnit_det_of_isUpperTriangular hXu fun r => ?_
    rw [hXdef, hP, rowsFrom, Matrix.add_apply, Matrix.sub_apply, diagonal_mul, one_apply_eq,
      diagonal_apply_eq]
    split_ifs
    · simpa using borel_diag_ne_zero hb r
    · simp
  have hY : IsUnit Y.det := by
    refine isUnit_det_of_isUpperTriangular hYu fun r => ?_
    rw [hYdef, hE, colsTo, Matrix.add_apply, Matrix.sub_apply, mul_diagonal, one_apply_eq,
      diagonal_apply_eq]
    split_ifs
    · simpa using borel_diag_ne_zero hb' r
    · simp
  unfold llRank
  rw [← hP, ← hE, key, rank_mul_eq_left_of_isUnit_det Y _ hY,
    rank_mul_eq_right_of_isUnit_det X _ hX]
end GroundTheory.Automorphic.Whittaker
