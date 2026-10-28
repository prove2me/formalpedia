-- Prove2me | solution 1 for OAI.DimensionTen.Border.minors_embedding_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:01:59.861864+00:00
-- url     : https://prove2.me/submissions/8d011c54-63b2-4c02-948d-4ca4e459dfc4

import Mathlib
import Definitions.Def_OAIQ057D011
import Theorems.Thm_OAI_DimensionTen_Border_high_alpha_s2

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_BorderData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border
lemma relation_row0 : ∀ k : Fin 20, (H * Cnum) 0 k = (-(d • D)) 0 k := by decide +kernel
lemma relation_row1 : ∀ k : Fin 20, (H * Cnum) 1 k = (-(d • D)) 1 k := by decide +kernel
lemma relation_row2 : ∀ k : Fin 20, (H * Cnum) 2 k = (-(d • D)) 2 k := by decide +kernel
lemma relation_row3 : ∀ k : Fin 20, (H * Cnum) 3 k = (-(d • D)) 3 k := by decide +kernel
lemma relation_row4 : ∀ k : Fin 20, (H * Cnum) 4 k = (-(d • D)) 4 k := by decide +kernel
lemma relation_row5 : ∀ k : Fin 20, (H * Cnum) 5 k = (-(d • D)) 5 k := by decide +kernel
lemma relation_row6 : ∀ k : Fin 20, (H * Cnum) 6 k = (-(d • D)) 6 k := by decide +kernel
lemma relation_row7 : ∀ k : Fin 20, (H * Cnum) 7 k = (-(d • D)) 7 k := by decide +kernel
lemma relation_row8 : ∀ k : Fin 20, (H * Cnum) 8 k = (-(d • D)) 8 k := by decide +kernel
lemma relation_row9 : ∀ k : Fin 20, (H * Cnum) 9 k = (-(d • D)) 9 k := by decide +kernel
lemma relation_row10 : ∀ k : Fin 20, (H * Cnum) 10 k = (-(d • D)) 10 k := by decide +kernel
lemma relation_row11 : ∀ k : Fin 20, (H * Cnum) 11 k = (-(d • D)) 11 k := by decide +kernel
lemma relation_row12 : ∀ k : Fin 20, (H * Cnum) 12 k = (-(d • D)) 12 k := by decide +kernel
lemma relation_row13 : ∀ k : Fin 20, (H * Cnum) 13 k = (-(d • D)) 13 k := by decide +kernel
lemma relation_row14 : ∀ k : Fin 20, (H * Cnum) 14 k = (-(d • D)) 14 k := by decide +kernel
lemma relation : H * Cnum = -(d • D) := by
  ext i j
  fin_cases i
  · exact relation_row0 j
  · exact relation_row1 j
  · exact relation_row2 j
  · exact relation_row3 j
  · exact relation_row4 j
  · exact relation_row5 j
  · exact relation_row6 j
  · exact relation_row7 j
  · exact relation_row8 j
  · exact relation_row9 j
  · exact relation_row10 j
  · exact relation_row11 j
  · exact relation_row12 j
  · exact relation_row13 j
  · exact relation_row14 j

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_MinorData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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

lemma minors_row_0 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 0 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 0 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) = (((1296 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((7344 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((8640 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((4212 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((23832 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((14400 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-13608 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-11232 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-6480 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-6240 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-2988 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((5112 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((336 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-24012 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-60336 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((-34992 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((-13176 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((-19008 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((759 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((2858 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-6600 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-19920 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-9200 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((11442 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((4704 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-40512 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-26016 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((27900 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((23040 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-3744 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((22032 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((13824 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((5184 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_1 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 1 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 1 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((3456 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((864 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((1044 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-1260 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((792 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((720 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1368 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-6912 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((-7488 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((-2808 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((-9072 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-150 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-1044 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-144 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-1704 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-2304 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-2382 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((768 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-1752 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-8352 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-1188 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((7416 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-4176 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((3672 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((4320 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_2 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 2 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 2 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-216 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-216 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-3024 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-5400 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((3024 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-1332 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((1836 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-936 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1692 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((1512 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((7632 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((3456 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((864 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((216 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((180 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-1020 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((2328 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((2400 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((2526 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-384 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((2712 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((3408 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((5004 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((0 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-4464 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((2376 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-3456 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
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

lemma minors_row_4 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 4 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 4 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 2) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-3024 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-12096 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-6480 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-2160 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-4752 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((3240 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((5040 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-7560 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-4176 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((19512 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((38880 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((13536 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((22248 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((21168 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((5184 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((162 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-3078 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-5040 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((5328 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((3600 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-7722 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-17040 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((17592 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((16944 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-24804 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-27288 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((5760 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-22032 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-11232 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-5184 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
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

lemma minors_row_7 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 7 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 7 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-12 : R) * x 1) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-6264 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-15768 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-6912 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-8424 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((-7344 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-4932 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-22572 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-25416 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-8208 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-2196 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((3888 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((3168 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((10584 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((14256 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((5184 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((2088 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((3876 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-708 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-2976 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-1200 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((13704 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((52836 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((65904 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((22752 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((29700 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((79632 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((44352 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((22896 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((26784 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((5184 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
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

lemma minors_row_11 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 11 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 11 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-1512 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1944 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((-1728 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((6480 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((6912 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-1908 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-15228 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-22608 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-9072 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((2448 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((6120 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((2016 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((216 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((2826 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-1410 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-25464 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-30720 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-9600 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((3798 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-3972 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((-18048 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-10128 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((-6012 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-16416 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-9648 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-9288 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-8640 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_12 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 12 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 12 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((2592 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-216 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-2376 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-4320 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((-1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-1080 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((-1728 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((2592 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((1944 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-1332 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-612 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-1008 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-3960 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-2592 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-1044 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((792 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((72 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((-2736 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((2340 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((-1656 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((-4464 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((216 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((-4752 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_13 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 13 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 13 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 2) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-3024 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-11448 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-5832 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((-3240 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((6264 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((7776 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((2592 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((3240 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((9468 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((3780 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-1368 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((-432 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((4752 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((15012 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((24120 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((8928 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((2592 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((4752 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((-1944 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

lemma minors_row_14 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x 14 = ((D.map (Int.castRingHom R)) *ᵥ homogeneousLow x +
      (H.map (Int.castRingHom R)) *ᵥ high (fun j => x j.succ)) 14 := by
  rw [minor, pencilR_eq, det_four, homogeneousLow_eq, high_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.map_apply, Pi.add_apply]
  change ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((-2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) - ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((-3 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) + ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2) * ((-6 : R) * x 1) + ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) - ((6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3) * ((6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) - ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) + ((6 : R) * x 3) * ((-3 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3) - ((6 : R) * x 3) * ((2 : R) * x 2 + (-4 : R) * x 3) * ((6 : R) * x 1) * ((-6 : R) * x 1) - ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1 + (6 : R) * x 3) * ((-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3) + ((6 : R) * x 3) * ((6 : R) * x 3) * ((6 : R) * x 3) * ((-6 : R) * x 1) = (((0 : ℤ) : R) * (x 0 ^ 4 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 0) + (((0 : ℤ) : R) * (x 0 ^ 3 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 0) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 2) + (((-1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 1) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 0) + (((1296 : ℤ) : R) * (x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 0) + (((-7776 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 3) + (((-17064 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 2) + (((-7992 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 1) + (((0 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 0) + (((648 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 2) + (((9720 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 1) + (((6048 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 0) + (((11016 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 1) + (((10368 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 0) + (((3888 : ℤ) : R) * (x 0 ^ 1 * x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))))))) + (((-9108 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 0 * x 3 ^ 4) + (((-31644 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 1 * x 3 ^ 3) + (((-33048 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 2 * x 3 ^ 2) + (((-10152 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 3 * x 3 ^ 1) + (((144 : ℤ) : R) * (x 1 ^ 0 * x 2 ^ 4 * x 3 ^ 0) + (((-8928 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 0 * x 3 ^ 3) + (((-11268 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 1 * x 3 ^ 2) + (((5544 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 2 * x 3 ^ 1) + (((5904 : ℤ) : R) * (x 1 ^ 1 * x 2 ^ 3 * x 3 ^ 0) + (((8604 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 0 * x 3 ^ 2) + (((26424 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 1 * x 3 ^ 1) + (((14112 : ℤ) : R) * (x 1 ^ 2 * x 2 ^ 2 * x 3 ^ 0) + (((11232 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 0 * x 3 ^ 1) + (((10800 : ℤ) : R) * (x 1 ^ 3 * x 2 ^ 1 * x 3 ^ 0) + (((2592 : ℤ) : R) * (x 1 ^ 4 * x 2 ^ 0 * x 3 ^ 0) + (0))))))))))))))))
  norm_num
  ring

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_MinorRelations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma minors_eq {R : Type*} [CommRing R] (x : Fin 4 → R) :
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

lemma homogeneousLow_chart {R : Type*} [CommRing R] (t : Fin 3 → R) :
    homogeneousLow (Fin.cons 1 t) = low t := by
  ext i
  simp [homogeneousLow]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_AlphaMinors
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma C_relation : H.map (Int.castRingHom ℚ) * C = -(D.map (Int.castRingHom ℚ)) := by
  have h := congrArg (fun A : Matrix (Fin 15) (Fin 20) ℤ => A.map (Int.castRingHom ℚ)) relation
  have hc : H.map (Int.castRingHom ℚ) * Cnum.map (Int.castRingHom ℚ) =
      -((d : ℚ) • D.map (Int.castRingHom ℚ)) := by
    rw [Matrix.map_mul] at h
    exact h.trans (by ext i j; simp [Matrix.map_apply, smul_eq_mul])
  rw [C, Matrix.mul_smul, hc, smul_neg, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

lemma map_int_rat {R m n : Type*} [Ring R] [Algebra ℚ R]
    (A : Matrix m n ℤ) : (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ R) =
      A.map (Int.castRingHom R) := by
  ext i j
  simp

lemma minors_alpha : minor (Fin.cons 1 alpha) = 0 := by
  have hc := congrArg (fun A : Matrix (Fin 15) (Fin 20) ℚ => A.map (algebraMap ℚ L)) C_relation
  have hcL : H.map (Int.castRingHom L) * C.map (algebraMap ℚ L) =
      -(D.map (Int.castRingHom L)) := by
    rw [Matrix.map_mul] at hc
    have hr : (-D.map (Int.castRingHom ℚ)).map (algebraMap ℚ L) =
        -(D.map (Int.castRingHom L)) := by ext i j; simp
    rw [map_int_rat, hr] at hc
    exact hc
  rw [minors_eq, homogeneousLow_chart]
  change D.map (Int.castRingHom L) *ᵥ low alpha + H.map (Int.castRingHom L) *ᵥ high alpha = 0
  rw [high_alpha_s2, Matrix.mulVec_mulVec, hcL,
    Matrix.neg_mulVec, add_neg_cancel]

lemma pencilR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) : (pencilR x).map f = pencilR (fun j => f (x j)) := by
  ext i j
  simp [pencilR, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma minor_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) (i : Fin 15) : f (minor x i) = minor (fun j => f (x j)) i := by
  rw [minor, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, pencilR_map]
  rfl

lemma minors_embedding_s2_oai {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    minor (Fin.cons 1 (fun j => σ (alpha j))) = 0 := by
  ext i
  have h := congrArg σ (congrFun minors_alpha i)
  change σ.toRingHom (minor (Fin.cons 1 alpha) i) = σ.toRingHom 0 at h
  rw [minor_map σ.toRingHom] at h
  have he : (fun j : Fin 4 => σ ((Fin.cons (α := fun _ => L) 1 alpha) j)) = Fin.cons 1 (fun j => σ (alpha j)) := by
    ext j
    refine Fin.cases (by simp) (fun k => rfl) j
  change minor (fun j : Fin 4 => σ ((Fin.cons (α := fun _ => L) 1 alpha) j)) i = σ 0 at h
  rw [he, map_zero] at h
  exact h

end DimensionTen.Border

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Border.minors_embedding_s2_oai.{u_1} := @OAI.DimensionTen.Border.minors_embedding_s2_oai.{u_1}
