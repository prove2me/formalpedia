-- Prove2me | solution 1 for OAI.DimensionTen.Border.minors_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:36:44.419893+00:00
-- url     : https://prove2.me/submissions/7e47c185-1de4-4e50-a9d9-a591a0491c57

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D014
import Theorems.Thm_OAI_DimensionTen_Border_minors_eq

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderData
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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_NormalizedMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma cast_mulVec (B : Matrix (Fin 20) (Fin 20) ℤ) (v : Fin 20 → ℤ) :
    (fun j => ((B *ᵥ v) j : ℚ)) = B.map (Int.castRingHom ℚ) *ᵥ (fun j => (v j : ℚ)) := by
  ext j
  exact (Int.castRingHom ℚ).map_mulVec B v j

lemma cast_single (i : Fin 20) :
    (fun j => ((Pi.single i 1 : Fin 20 → ℤ) j : ℚ)) = eQ i := by
  ext j
  simp [eQ, Pi.single_apply]

lemma normalize_shift (B : Matrix (Fin 20) (Fin 20) ℤ) (i j : Fin 20)
    (h : B *ᵥ Pi.single i 1 = d • Pi.single j 1) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ i = eQ j := by
  have hh := congrArg (fun v : Fin 20 → ℤ => fun k => (v k : ℚ)) h
  rw [cast_mulVec, cast_single] at hh
  have hcast : (fun k => ((d • (Pi.single j 1 : Fin 20 → ℤ)) k : ℚ)) = (d : ℚ) • eQ j := by
    ext k
    simp [eQ, Pi.single_apply, smul_eq_mul]
  rw [hcast] at hh
  rw [Matrix.smul_mulVec, hh, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderField
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma E_one : E 1 = eQ 0 := by change rho 1 *ᵥ eQ 0 = _; simp
lemma E_mul (a b : L) : E (a * b) = rho a *ᵥ E b := by
  change rho (a * b) *ᵥ eQ 0 = rho a *ᵥ (rho b *ᵥ eQ 0)
  rw [map_mul, Matrix.mulVec_mulVec]

lemma rho_alpha (i : Fin 3) : rho (alpha i) = NB i := by
  fin_cases i
  · change rho ((d : ℚ)⁻¹ • AdjoinRoot.root fQ) = _
    rw [map_smul, rho_root]
    rfl
  · exact (NB_in_image 1).choose_spec
  · exact (NB_in_image 2).choose_spec

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_LowBasis
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma low_zero {R : Type*} [CommRing R] (t : Fin 3 → R) : low t 0 = 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma low_shift_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 1 = t 2 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_1 : NB 2 *ᵥ eQ 0 = eQ 1 := by
  exact normalize_shift B2 0 1 shift_1

lemma low_shift_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 2 = t 1 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_2 : NB 1 *ᵥ eQ 0 = eQ 2 := by
  exact normalize_shift B1 0 2 shift_2

lemma low_shift_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 3 = t 0 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_3 : NB 0 *ᵥ eQ 0 = eQ 3 := by
  exact normalize_shift B0 0 3 shift_3

lemma low_shift_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 4 = t 2 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_4 : NB 2 *ᵥ eQ 1 = eQ 4 := by
  exact normalize_shift B2 1 4 shift_4

lemma low_shift_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 5 = t 1 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_5 : NB 1 *ᵥ eQ 1 = eQ 5 := by
  exact normalize_shift B1 1 5 shift_5

lemma low_shift_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 6 = t 1 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_6 : NB 1 *ᵥ eQ 2 = eQ 6 := by
  exact normalize_shift B1 2 6 shift_6

lemma low_shift_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 7 = t 0 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_7 : NB 0 *ᵥ eQ 1 = eQ 7 := by
  exact normalize_shift B0 1 7 shift_7

lemma low_shift_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 8 = t 0 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_8 : NB 0 *ᵥ eQ 2 = eQ 8 := by
  exact normalize_shift B0 2 8 shift_8

lemma low_shift_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 9 = t 0 * low t 3 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_9 : NB 0 *ᵥ eQ 3 = eQ 9 := by
  exact normalize_shift B0 3 9 shift_9

lemma low_shift_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 10 = t 2 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_10 : NB 2 *ᵥ eQ 4 = eQ 10 := by
  exact normalize_shift B2 4 10 shift_10

lemma low_shift_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 11 = t 1 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_11 : NB 1 *ᵥ eQ 4 = eQ 11 := by
  exact normalize_shift B1 4 11 shift_11

lemma low_shift_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 12 = t 1 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_12 : NB 1 *ᵥ eQ 5 = eQ 12 := by
  exact normalize_shift B1 5 12 shift_12

lemma low_shift_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 13 = t 1 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_13 : NB 1 *ᵥ eQ 6 = eQ 13 := by
  exact normalize_shift B1 6 13 shift_13

lemma low_shift_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 14 = t 0 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_14 : NB 0 *ᵥ eQ 4 = eQ 14 := by
  exact normalize_shift B0 4 14 shift_14

lemma low_shift_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 15 = t 0 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_15 : NB 0 *ᵥ eQ 5 = eQ 15 := by
  exact normalize_shift B0 5 15 shift_15

lemma low_shift_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 16 = t 0 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_16 : NB 0 *ᵥ eQ 6 = eQ 16 := by
  exact normalize_shift B0 6 16 shift_16

lemma low_shift_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 17 = t 0 * low t 7 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_17 : NB 0 *ᵥ eQ 7 = eQ 17 := by
  exact normalize_shift B0 7 17 shift_17

lemma low_shift_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 18 = t 0 * low t 8 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_18 : NB 0 *ᵥ eQ 8 = eQ 18 := by
  exact normalize_shift B0 8 18 shift_18

lemma low_shift_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 19 = t 0 * low t 9 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_19 : NB 0 *ᵥ eQ 9 = eQ 19 := by
  exact normalize_shift B0 9 19 shift_19

lemma E_low_0 : E (low alpha 0) = eQ 0 := by rw [low_zero, E_one]

lemma E_low_1 : E (low alpha 1) = eQ 1 := by
  rw [low_shift_1, E_mul, rho_alpha, E_low_0, NB_shift_1]

lemma E_low_2 : E (low alpha 2) = eQ 2 := by
  rw [low_shift_2, E_mul, rho_alpha, E_low_0, NB_shift_2]

lemma E_low_3 : E (low alpha 3) = eQ 3 := by
  rw [low_shift_3, E_mul, rho_alpha, E_low_0, NB_shift_3]

lemma E_low_4 : E (low alpha 4) = eQ 4 := by
  rw [low_shift_4, E_mul, rho_alpha, E_low_1, NB_shift_4]

lemma E_low_5 : E (low alpha 5) = eQ 5 := by
  rw [low_shift_5, E_mul, rho_alpha, E_low_1, NB_shift_5]

lemma E_low_6 : E (low alpha 6) = eQ 6 := by
  rw [low_shift_6, E_mul, rho_alpha, E_low_2, NB_shift_6]

lemma E_low_7 : E (low alpha 7) = eQ 7 := by
  rw [low_shift_7, E_mul, rho_alpha, E_low_1, NB_shift_7]

lemma E_low_8 : E (low alpha 8) = eQ 8 := by
  rw [low_shift_8, E_mul, rho_alpha, E_low_2, NB_shift_8]

lemma E_low_9 : E (low alpha 9) = eQ 9 := by
  rw [low_shift_9, E_mul, rho_alpha, E_low_3, NB_shift_9]

lemma E_low_10 : E (low alpha 10) = eQ 10 := by
  rw [low_shift_10, E_mul, rho_alpha, E_low_4, NB_shift_10]

lemma E_low_11 : E (low alpha 11) = eQ 11 := by
  rw [low_shift_11, E_mul, rho_alpha, E_low_4, NB_shift_11]

lemma E_low_12 : E (low alpha 12) = eQ 12 := by
  rw [low_shift_12, E_mul, rho_alpha, E_low_5, NB_shift_12]

lemma E_low_13 : E (low alpha 13) = eQ 13 := by
  rw [low_shift_13, E_mul, rho_alpha, E_low_6, NB_shift_13]

lemma E_low_14 : E (low alpha 14) = eQ 14 := by
  rw [low_shift_14, E_mul, rho_alpha, E_low_4, NB_shift_14]

lemma E_low_15 : E (low alpha 15) = eQ 15 := by
  rw [low_shift_15, E_mul, rho_alpha, E_low_5, NB_shift_15]

lemma E_low_16 : E (low alpha 16) = eQ 16 := by
  rw [low_shift_16, E_mul, rho_alpha, E_low_6, NB_shift_16]

lemma E_low_17 : E (low alpha 17) = eQ 17 := by
  rw [low_shift_17, E_mul, rho_alpha, E_low_7, NB_shift_17]

lemma E_low_18 : E (low alpha 18) = eQ 18 := by
  rw [low_shift_18, E_mul, rho_alpha, E_low_8, NB_shift_18]

lemma E_low_19 : E (low alpha 19) = eQ 19 := by
  rw [low_shift_19, E_mul, rho_alpha, E_low_9, NB_shift_19]

lemma E_low (i : Fin 20) : E (low alpha i) = eQ i := by
  fin_cases i
  · exact E_low_0
  · exact E_low_1
  · exact E_low_2
  · exact E_low_3
  · exact E_low_4
  · exact E_low_5
  · exact E_low_6
  · exact E_low_7
  · exact E_low_8
  · exact E_low_9
  · exact E_low_10
  · exact E_low_11
  · exact E_low_12
  · exact E_low_13
  · exact E_low_14
  · exact E_low_15
  · exact E_low_16
  · exact E_low_17
  · exact E_low_18
  · exact E_low_19


end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderRelations
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma normalize_border (B : Matrix (Fin 20) (Fin 20) ℤ) (i : Fin 15) (k : Fin 20)
    (h : ∀ m, B m k = Cnum i m) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ k = C i := by
  ext m
  simp only [eQ, Matrix.mulVec_single_one, Matrix.smul_apply, Matrix.map_apply,
    Matrix.col_apply, C, smul_eq_mul]
  rw [h m]

lemma E_sum (c : Fin 20 → ℚ) : E (∑ m, c m • low alpha m) = c := by
  ext k
  simp [map_sum, E_low, eQ, Pi.single_apply]

lemma high_shift_0 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 0 = t 2 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_0 : ∀ m : Fin 20, B2 m 10 = Cnum 0 m := by decide +kernel

lemma NB_border_0 : NB 2 *ᵥ eQ 10 = C 0 := by
  exact normalize_border B2 0 10 border_column_0

lemma high_relation_0 : high alpha 0 = ∑ m, C 0 m • low alpha m := by
  apply E_injective
  rw [high_shift_0, E_mul, rho_alpha, E_low, NB_border_0, E_sum]

lemma high_shift_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 1 = t 1 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_1 : ∀ m : Fin 20, B1 m 10 = Cnum 1 m := by decide +kernel

lemma NB_border_1 : NB 1 *ᵥ eQ 10 = C 1 := by
  exact normalize_border B1 1 10 border_column_1

lemma high_relation_1 : high alpha 1 = ∑ m, C 1 m • low alpha m := by
  apply E_injective
  rw [high_shift_1, E_mul, rho_alpha, E_low, NB_border_1, E_sum]

lemma high_shift_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 2 = t 1 * low t 11 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_2 : ∀ m : Fin 20, B1 m 11 = Cnum 2 m := by decide +kernel

lemma NB_border_2 : NB 1 *ᵥ eQ 11 = C 2 := by
  exact normalize_border B1 2 11 border_column_2

lemma high_relation_2 : high alpha 2 = ∑ m, C 2 m • low alpha m := by
  apply E_injective
  rw [high_shift_2, E_mul, rho_alpha, E_low, NB_border_2, E_sum]

lemma high_shift_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 3 = t 1 * low t 12 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_3 : ∀ m : Fin 20, B1 m 12 = Cnum 3 m := by decide +kernel

lemma NB_border_3 : NB 1 *ᵥ eQ 12 = C 3 := by
  exact normalize_border B1 3 12 border_column_3

lemma high_relation_3 : high alpha 3 = ∑ m, C 3 m • low alpha m := by
  apply E_injective
  rw [high_shift_3, E_mul, rho_alpha, E_low, NB_border_3, E_sum]

lemma high_shift_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 4 = t 1 * low t 13 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_4 : ∀ m : Fin 20, B1 m 13 = Cnum 4 m := by decide +kernel

lemma NB_border_4 : NB 1 *ᵥ eQ 13 = C 4 := by
  exact normalize_border B1 4 13 border_column_4

lemma high_relation_4 : high alpha 4 = ∑ m, C 4 m • low alpha m := by
  apply E_injective
  rw [high_shift_4, E_mul, rho_alpha, E_low, NB_border_4, E_sum]

lemma high_shift_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 5 = t 0 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_5 : ∀ m : Fin 20, B0 m 10 = Cnum 5 m := by decide +kernel

lemma NB_border_5 : NB 0 *ᵥ eQ 10 = C 5 := by
  exact normalize_border B0 5 10 border_column_5

lemma high_relation_5 : high alpha 5 = ∑ m, C 5 m • low alpha m := by
  apply E_injective
  rw [high_shift_5, E_mul, rho_alpha, E_low, NB_border_5, E_sum]

lemma high_shift_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 6 = t 0 * low t 11 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_6 : ∀ m : Fin 20, B0 m 11 = Cnum 6 m := by decide +kernel

lemma NB_border_6 : NB 0 *ᵥ eQ 11 = C 6 := by
  exact normalize_border B0 6 11 border_column_6

lemma high_relation_6 : high alpha 6 = ∑ m, C 6 m • low alpha m := by
  apply E_injective
  rw [high_shift_6, E_mul, rho_alpha, E_low, NB_border_6, E_sum]

lemma high_shift_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 7 = t 0 * low t 12 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_7 : ∀ m : Fin 20, B0 m 12 = Cnum 7 m := by decide +kernel

lemma NB_border_7 : NB 0 *ᵥ eQ 12 = C 7 := by
  exact normalize_border B0 7 12 border_column_7

lemma high_relation_7 : high alpha 7 = ∑ m, C 7 m • low alpha m := by
  apply E_injective
  rw [high_shift_7, E_mul, rho_alpha, E_low, NB_border_7, E_sum]

lemma high_shift_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 8 = t 0 * low t 13 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_8 : ∀ m : Fin 20, B0 m 13 = Cnum 8 m := by decide +kernel

lemma NB_border_8 : NB 0 *ᵥ eQ 13 = C 8 := by
  exact normalize_border B0 8 13 border_column_8

lemma high_relation_8 : high alpha 8 = ∑ m, C 8 m • low alpha m := by
  apply E_injective
  rw [high_shift_8, E_mul, rho_alpha, E_low, NB_border_8, E_sum]

lemma high_shift_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 9 = t 0 * low t 14 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_9 : ∀ m : Fin 20, B0 m 14 = Cnum 9 m := by decide +kernel

lemma NB_border_9 : NB 0 *ᵥ eQ 14 = C 9 := by
  exact normalize_border B0 9 14 border_column_9

lemma high_relation_9 : high alpha 9 = ∑ m, C 9 m • low alpha m := by
  apply E_injective
  rw [high_shift_9, E_mul, rho_alpha, E_low, NB_border_9, E_sum]

lemma high_shift_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 10 = t 0 * low t 15 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_10 : ∀ m : Fin 20, B0 m 15 = Cnum 10 m := by decide +kernel

lemma NB_border_10 : NB 0 *ᵥ eQ 15 = C 10 := by
  exact normalize_border B0 10 15 border_column_10

lemma high_relation_10 : high alpha 10 = ∑ m, C 10 m • low alpha m := by
  apply E_injective
  rw [high_shift_10, E_mul, rho_alpha, E_low, NB_border_10, E_sum]

lemma high_shift_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 11 = t 0 * low t 16 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_11 : ∀ m : Fin 20, B0 m 16 = Cnum 11 m := by decide +kernel

lemma NB_border_11 : NB 0 *ᵥ eQ 16 = C 11 := by
  exact normalize_border B0 11 16 border_column_11

lemma high_relation_11 : high alpha 11 = ∑ m, C 11 m • low alpha m := by
  apply E_injective
  rw [high_shift_11, E_mul, rho_alpha, E_low, NB_border_11, E_sum]

lemma high_shift_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 12 = t 0 * low t 17 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_12 : ∀ m : Fin 20, B0 m 17 = Cnum 12 m := by decide +kernel

lemma NB_border_12 : NB 0 *ᵥ eQ 17 = C 12 := by
  exact normalize_border B0 12 17 border_column_12

lemma high_relation_12 : high alpha 12 = ∑ m, C 12 m • low alpha m := by
  apply E_injective
  rw [high_shift_12, E_mul, rho_alpha, E_low, NB_border_12, E_sum]

lemma high_shift_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 13 = t 0 * low t 18 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_13 : ∀ m : Fin 20, B0 m 18 = Cnum 13 m := by decide +kernel

lemma NB_border_13 : NB 0 *ᵥ eQ 18 = C 13 := by
  exact normalize_border B0 13 18 border_column_13

lemma high_relation_13 : high alpha 13 = ∑ m, C 13 m • low alpha m := by
  apply E_injective
  rw [high_shift_13, E_mul, rho_alpha, E_low, NB_border_13, E_sum]

lemma high_shift_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 14 = t 0 * low t 19 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_14 : ∀ m : Fin 20, B0 m 19 = Cnum 14 m := by decide +kernel

lemma NB_border_14 : NB 0 *ᵥ eQ 19 = C 14 := by
  exact normalize_border B0 14 19 border_column_14

lemma high_relation_14 : high alpha 14 = ∑ m, C 14 m • low alpha m := by
  apply E_injective
  rw [high_shift_14, E_mul, rho_alpha, E_low, NB_border_14, E_sum]

lemma high_relation (i : Fin 15) : high alpha i = ∑ m, C i m • low alpha m := by
  fin_cases i
  · exact high_relation_0
  · exact high_relation_1
  · exact high_relation_2
  · exact high_relation_3
  · exact high_relation_4
  · exact high_relation_5
  · exact high_relation_6
  · exact high_relation_7
  · exact high_relation_8
  · exact high_relation_9
  · exact high_relation_10
  · exact high_relation_11
  · exact high_relation_12
  · exact high_relation_13
  · exact high_relation_14

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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_AlphaMinors
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK
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

lemma high_alpha : high alpha = C.map (algebraMap ℚ L) *ᵥ low alpha := by
  ext i
  rw [high_relation]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]
  congr 1

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
  rw [high_alpha, Matrix.mulVec_mulVec, hcL,
    Matrix.neg_mulVec, add_neg_cancel]

lemma pencilR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) : (pencilR x).map f = pencilR (fun j => f (x j)) := by
  ext i j
  simp [pencilR, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma minor_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 4 → R) (i : Fin 15) : f (minor x i) = minor (fun j => f (x j)) i := by
  rw [minor, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, pencilR_map]
  rfl

lemma minors_embedding_oai {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
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

theorem solution.{u_1} : type_of% @OAI.DimensionTen.Border.minors_embedding_oai.{u_1} := @OAI.DimensionTen.Border.minors_embedding_oai.{u_1}
