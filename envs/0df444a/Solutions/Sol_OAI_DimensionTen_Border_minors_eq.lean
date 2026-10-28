-- Prove2me | solution 1 for OAI.DimensionTen.Border.minors_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:05:48.398288+00:00
-- url     : https://prove2.me/submissions/4a69aaaa-cb69-4ba0-b9a9-27a301daf9dc

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D012
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_0
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_11
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_12
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_13
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_14
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_2
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_4
import Theorems.Thm_OAI_DimensionTen_Border_minors_row_7

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_MinorData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma pencil_entry_0_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 0 0 = pencilExplicit x 0 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((6 : ℤ) : R) + (x 1 * ((-12 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (6 : R) * x 0 + (-12 : R) * x 1
    norm_num
    ring

lemma pencil_entry_0_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 0 1 = pencilExplicit x 0 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((6 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (6 : R) * x 2
    norm_num
    ring

lemma pencil_entry_0_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 0 2 = pencilExplicit x 0 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((-2 : ℤ) : R) + (x 3 * ((-4 : ℤ) : R) + (0)))) = (-2 : R) * x 2 + (-4 : R) * x 3
    norm_num
    ring

lemma pencil_entry_0_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 0 3 = pencilExplicit x 0 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((-3 : ℤ) : R) + (0)))) = (-3 : R) * x 3
    norm_num
    ring

lemma pencil_entry_1_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 1 0 = pencilExplicit x 1 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((6 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (6 : R) * x 2
    norm_num
    ring

lemma pencil_entry_1_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 1 1 = pencilExplicit x 1 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((6 : ℤ) : R) + (x 1 * ((-6 : ℤ) : R) + (x 2 * ((6 : ℤ) : R) + (x 3 * ((-2 : ℤ) : R) + (0)))) = (6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3
    norm_num
    ring

lemma pencil_entry_1_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 1 2 = pencilExplicit x 1 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((-3 : ℤ) : R) + (0)))) = (-3 : R) * x 3
    norm_num
    ring

lemma pencil_entry_1_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 1 3 = pencilExplicit x 1 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((2 : ℤ) : R) + (x 3 * ((-4 : ℤ) : R) + (0)))) = (2 : R) * x 2 + (-4 : R) * x 3
    norm_num
    ring

lemma pencil_entry_2_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 2 0 = pencilExplicit x 2 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((-2 : ℤ) : R) + (x 3 * ((-4 : ℤ) : R) + (0)))) = (-2 : R) * x 2 + (-4 : R) * x 3
    norm_num
    ring

lemma pencil_entry_2_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 2 1 = pencilExplicit x 2 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((-3 : ℤ) : R) + (0)))) = (-3 : R) * x 3
    norm_num
    ring

lemma pencil_entry_2_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 2 2 = pencilExplicit x 2 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((6 : ℤ) : R) + (x 1 * ((6 : ℤ) : R) + (x 2 * ((10 : ℤ) : R) + (x 3 * ((11 : ℤ) : R) + (0)))) = (6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3
    norm_num
    ring

lemma pencil_entry_2_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 2 3 = pencilExplicit x 2 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_3_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 3 0 = pencilExplicit x 3 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((-3 : ℤ) : R) + (0)))) = (-3 : R) * x 3
    norm_num
    ring

lemma pencil_entry_3_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 3 1 = pencilExplicit x 3 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((2 : ℤ) : R) + (x 3 * ((-4 : ℤ) : R) + (0)))) = (2 : R) * x 2 + (-4 : R) * x 3
    norm_num
    ring

lemma pencil_entry_3_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 3 2 = pencilExplicit x 3 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_3_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 3 3 = pencilExplicit x 3 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((6 : ℤ) : R) + (x 1 * ((12 : ℤ) : R) + (x 2 * ((24 : ℤ) : R) + (x 3 * ((25 : ℤ) : R) + (0)))) = (6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3
    norm_num
    ring

lemma pencil_entry_4_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 4 0 = pencilExplicit x 4 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((-6 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (-6 : R) * x 1 + (6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_4_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 4 1 = pencilExplicit x 4 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_4_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 4 2 = pencilExplicit x 4 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((6 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (6 : R) * x 1
    norm_num
    ring

lemma pencil_entry_4_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 4 3 = pencilExplicit x 4 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((6 : ℤ) : R) + (x 2 * ((6 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (6 : R) * x 1 + (6 : R) * x 2
    norm_num
    ring

lemma pencil_entry_5_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 5 0 = pencilExplicit x 5 0 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((-6 : ℤ) : R) + (x 2 * ((0 : ℤ) : R) + (x 3 * ((0 : ℤ) : R) + (0)))) = (-6 : R) * x 1
    norm_num
    ring

lemma pencil_entry_5_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 5 1 = pencilExplicit x 5 1 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((-6 : ℤ) : R) + (x 2 * ((-6 : ℤ) : R) + (x 3 * ((-6 : ℤ) : R) + (0)))) = (-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_5_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 5 2 = pencilExplicit x 5 2 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((6 : ℤ) : R) + (x 2 * ((6 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3
    norm_num
    ring

lemma pencil_entry_5_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
      pencilR x 5 3 = pencilExplicit x 5 3 := by
    simp only [pencilR, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
    change x 0 * ((0 : ℤ) : R) + (x 1 * ((0 : ℤ) : R) + (x 2 * ((-6 : ℤ) : R) + (x 3 * ((6 : ℤ) : R) + (0)))) = (-6 : R) * x 2 + (6 : R) * x 3
    norm_num
    ring

lemma pencilR_eq {R : Type*} [CommRing R] (x : Fin 4 → R) : pencilR x = pencilExplicit x := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact pencil_entry_0_0 x
  · exact pencil_entry_0_1 x
  · exact pencil_entry_0_2 x
  · exact pencil_entry_0_3 x
  · exact pencil_entry_1_0 x
  · exact pencil_entry_1_1 x
  · exact pencil_entry_1_2 x
  · exact pencil_entry_1_3 x
  · exact pencil_entry_2_0 x
  · exact pencil_entry_2_1 x
  · exact pencil_entry_2_2 x
  · exact pencil_entry_2_3 x
  · exact pencil_entry_3_0 x
  · exact pencil_entry_3_1 x
  · exact pencil_entry_3_2 x
  · exact pencil_entry_3_3 x
  · exact pencil_entry_4_0 x
  · exact pencil_entry_4_1 x
  · exact pencil_entry_4_2 x
  · exact pencil_entry_4_3 x
  · exact pencil_entry_5_0 x
  · exact pencil_entry_5_1 x
  · exact pencil_entry_5_2 x
  · exact pencil_entry_5_3 x

 lemma det_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
     M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2 - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1 + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1 - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2 + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0 - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0 + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1 - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0 + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0 - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1 + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0 - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

lemma homogeneousLow_eq {R : Type*} [CommRing R] (x : Fin 4 → R) :
    homogeneousLow x = ![x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0, x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1, x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0, x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0, x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2, x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1, x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0, x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1, x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0, x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0, x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3, x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2, x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1, x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0, x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2, x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1, x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0, x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1, x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0, x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0] := by
  ext i; fin_cases i <;> simp [homogeneousLow, low, mon, monExps, Fin.prod_univ_succ, Fin.sum_univ_succ, mul_assoc]

lemma high_eq {R : Type*} [CommRing R] (x : Fin 4 → R) :
    high (fun j => x j.succ) = ![x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4, x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3, x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2, x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1, x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0, x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3, x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2, x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1, x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0, x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2, x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1, x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0, x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1, x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0, x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0] := by
  ext i; fin_cases i <;> simp [high, mon, monExps, Fin.prod_univ_succ, mul_assoc]

lemma minors_row_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 1 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 1 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((3456 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((864 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((1044 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-1260 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((792 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((720 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1368 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-6912 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((-7488 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((-2808 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((-9072 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-150 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-1044 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-144 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-1704 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-2304 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-2382 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((768 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-1752 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-8352 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-1188 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((7416 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-4176 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((3672 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((4320 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_3 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 3 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 3 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((864 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-2808 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-6048 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-4500 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-8784 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-432 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((3204 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-1944 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((-1584 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((13176 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((15984 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((5184 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((1026 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((3648 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((4116 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-1464 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-144 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((6084 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((14496 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((4992 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((6720 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-2124 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((4032 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((11808 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-11664 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-6048 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-5184 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_5 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 5 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 5 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-3888 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-1080 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-216 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1944 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((8424 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((1080 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((11232 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((3888 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-324 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((324 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((504 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-288 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((864 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((756 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((900 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-2160 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((6768 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((2988 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-9864 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((4608 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-6480 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_6 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 6 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 6 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((7776 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((6912 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-432 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((2808 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((864 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((8568 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((11088 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((1152 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-720 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-3492 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((6624 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((-6048 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((4320 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-438 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-10632 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-21168 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-9768 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((48 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-19122 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-47676 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-17040 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((8400 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-27144 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-23112 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((10944 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-9504 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((3456 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_8 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 8 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 8 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((432 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-3024 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-2160 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((2160 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-4320 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((-432 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((1512 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-288 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((576 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-2304 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-2880 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-288 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((1980 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-432 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((4752 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((7632 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((2844 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((9000 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((15696 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((4104 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((10800 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_9 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 9 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 9 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((4968 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((11448 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((3456 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-432 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((8640 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((14472 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((4752 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((4104 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((4320 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((2916 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((4788 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-5184 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-4032 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-9072 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-33228 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-10800 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((4608 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-29340 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-43704 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-7632 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-22032 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-15552 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-5184 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_10 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 10 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 10 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-7344 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-7992 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((3240 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((8208 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-5976 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-16740 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-8928 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-432 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((1260 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((16488 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((13248 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((1512 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((5616 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((2718 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((4830 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((2364 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((312 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-720 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((8640 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((23604 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((24288 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((5568 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((1872 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((5184 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((1152 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-6048 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-6048 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_MinorRelations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma minors_eq_oai {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x = D.map (Int.castRingHom R) *ᵥ homogeneousLow x +
      H.map (Int.castRingHom R) *ᵥ high (fun j => x j.succ) := by
  funext i
  fin_cases i
  · exact minors_row_0 x
  · exact minors_row_1 x
  · exact minors_row_2 x
  · exact minors_row_3 x
  · exact minors_row_4 x
  · exact minors_row_5 x
  · exact minors_row_6 x
  · exact minors_row_7 x
  · exact minors_row_8 x
  · exact minors_row_9 x
  · exact minors_row_10 x
  · exact minors_row_11 x
  · exact minors_row_12 x
  · exact minors_row_13 x
  · exact minors_row_14 x

end DimensionTen.Border

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Border.minors_eq_oai.{u_1} := @OAI.DimensionTen.Border.minors_eq_oai.{u_1}
