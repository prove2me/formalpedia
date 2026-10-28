-- Prove2me | solution 1 for OAI.DimensionTen.Border.minors_row_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:08:21.548557+00:00
-- url     : https://prove2.me/submissions/dca24447-0283-4ac2-b3be-4a834f24a6d6

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D012

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

lemma minors_row_12_oai {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 12 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 12 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-216 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-2376 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-4320 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1080 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((2592 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((1944 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-1332 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-612 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-1008 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-3960 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-2592 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-1044 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((792 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((72 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-2736 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((2340 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-1656 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-4464 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((216 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-4752 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

end DimensionTen.Border

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Border.minors_row_12_oai.{u_1} := @OAI.DimensionTen.Border.minors_row_12_oai.{u_1}
