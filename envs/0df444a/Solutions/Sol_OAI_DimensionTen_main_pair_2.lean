-- Prove2me | solution 2 for OAI.DimensionTen.main_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:53:02.90149+00:00
-- url     : https://prove2.me/submissions/c4fe652f-ce7a-4454-82ca-fbd36d1d7d78

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D009
import Definitions.Def_OAIQ033D014
import Theorems.Thm_OAI_DimensionTen_Border_minors_embedding
import Theorems.Thm_OAI_DimensionTen_Border_quadratic_zero_bound
import Theorems.Thm_OAI_DimensionTen_compositeChoi_kernel_rank
import Theorems.Thm_OAI_DimensionTen_compositeChoi_ne

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

lemma E_sum (c : Fin 20 → ℚ) : E (∑ m, c m • low alpha m) = c := by
  ext k
  simp [map_sum, E_low, eQ, Pi.single_apply]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen


theorem blocksZ_transpose_mul_comm (i j : Fin 4) :
    (blocksZ i)ᵀ * blocksZ j = (blocksZ j)ᵀ * blocksZ i := by
  decide +revert


theorem blocks_transpose_mul_comm (i j : Fin 4) :
    (blocks i)ᵀ * blocks j = (blocks j)ᵀ * blocks i := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ =>
    A.map (Int.castRingHom ℂ)) (blocksZ_transpose_mul_comm i j)
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

end DimensionTen

end
end

end OAI
end

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

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_AlphaMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma mon_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 35) : f (mon t i) = mon (fun j => f (t j)) i := by
  simp [mon]

lemma low_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) (i : Fin 20) : f (low t i) = low (fun j => f (t j)) i := by
  exact mon_map f t _

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Cofactors
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

lemma adjugate_updateRow_column {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i j : n) (u : n → R) :
    (A.updateRow i u).adjugate j i = A.adjugate j i := by
  simp only [Matrix.adjugate_apply]
  congr 1
  ext k l
  by_cases hk : k = i <;> simp [Matrix.updateRow_apply, hk]

lemma dot_adjugate_column {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i : n) (u : n → R) :
    dotProduct u (fun j => A.adjugate j i) = (A.updateRow i u).det := by
  rw [Matrix.det_eq_sum_mul_adjugate_row _ i]
  simp only [Matrix.updateRow_self, adjugate_updateRow_column, dotProduct]

lemma top_minors_kernel {R : Type*} [CommRing R] (M : Matrix (Fin 6) (Fin 4) R)
    (h : ∀ k : Fin 15, (M.submatrix (rowChoices k) id).det = 0) :
    M *ᵥ (fun j => (M.submatrix (rowChoices 0) id).adjugate j 3) = 0 := by
  ext i
  change dotProduct (M i) (fun j => (M.submatrix (rowChoices 0) id).adjugate j 3) = 0
  rw [dot_adjugate_column]
  fin_cases i
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 0) (j := 3) (by decide)
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 1) (j := 3) (by decide)
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 2) (j := 3) (by decide)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 3) =
        M.submatrix (rowChoices 0) id := by
      exact Matrix.updateRow_eq_self _ _
    exact (congrArg Matrix.det he).trans (h 0)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 4) =
        M.submatrix (rowChoices 1) id := by
      ext i j
      fin_cases i <;> simp [Matrix.updateRow, rowChoices, PencilAlgebra.rows]
    exact (congrArg Matrix.det he).trans (h 1)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 5) =
        M.submatrix (rowChoices 2) id := by
      ext i j
      fin_cases i <;> simp [Matrix.updateRow, rowChoices, PencilAlgebra.rows]
    exact (congrArg Matrix.det he).trans (h 2)

lemma cofactorKernel_eq_zero {R : Type*} [CommRing R] (x : Fin 4 → R)
    (h : minor x = 0) : pencilR x *ᵥ cofactorKernel x = 0 :=
  top_minors_kernel (pencilR x) (fun k => congrFun h k)

lemma rank_lt_of_kernel {R : Type*} [Field R] (M : Matrix (Fin 6) (Fin 4) R)
    (v : Fin 4 → R) (hv : v ≠ 0) (hm : M *ᵥ v = 0) : M.rank < 4 := by
  have hn : ¬ Function.Injective (fun w => M *ᵥ w) := by
    intro hh
    exact hv (hh (hm.trans (Matrix.mulVec_zero M).symm))
  have hr := Matrix.rank_le_width M
  have he : M.rank ≠ 4 := by
    intro h
    apply hn
    change Function.Injective (Matrix.mulVecLin M)
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    change M.rank + Module.finrank R (LinearMap.ker (Matrix.mulVecLin M)) =
      Module.finrank R (Fin 4 → R) at hdim
    simp only [h, Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  simpa only [Fintype.card_fin] using lt_of_le_of_ne hr he

end DimensionTen.Border

end
end

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma low_eq {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t = ![t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 2, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 2 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 1 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 2 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 3, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 2, t 0 ^ 0 * t 1 ^ 2 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 3 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 2, t 0 ^ 1 * t 1 ^ 1 * t 2 ^ 1, t 0 ^ 1 * t 1 ^ 2 * t 2 ^ 0, t 0 ^ 2 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 2 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 3 * t 1 ^ 0 * t 2 ^ 0] := by
  ext i
  fin_cases i <;> simp [low, mon, monExps, Fin.prod_univ_succ, mul_assoc]

lemma cofactor_chart_last {R : Type*} [CommRing R] (t : Fin 3 → R) :
    cofactorKernel (Fin.cons 1 t) 3 = ∑ i, (cofactorCoeffs i : R) * low t i := by
  rw [cofactorKernel, Matrix.adjugate_apply, pencilR_eq, det_four, low_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.updateRow_apply,
    Matrix.submatrix_apply, Pi.single_apply]
  have hc2 : Fin.cons (α := fun _ : Fin 4 => R) 1 t 2 = t 1 := rfl
  have hc3 : Fin.cons (α := fun _ : Fin 4 => R) 1 t 3 = t 2 := rfl
  simp [pencilExplicit, rowChoices, PencilAlgebra.rows, cofactorCoeffs, hc2, hc3]
  ring

lemma cofactor_alpha_last_ne : cofactorKernel (Fin.cons 1 alpha) 3 ≠ 0 := by
  intro h
  have hh : cofactorKernel (Fin.cons 1 alpha) 3 =
      ∑ i, (cofactorCoeffs i : ℚ) • low alpha i := by
    simpa only [Algebra.smul_def, map_intCast] using cofactor_chart_last alpha
  rw [hh] at h
  have hE := congrArg E h
  rw [E_sum, map_zero] at hE
  have hz := congrFun hE 0
  norm_num [cofactorCoeffs] at hz

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PureMatrices
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pure_posSemidef {n : Type*} [Fintype n] (x : n → ℂ) : (pure x).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

lemma product_dot {a b : ℕ} (x y : Fin a → ℂ) (u v : Fin b → ℂ) :
    star (productVector x u) ⬝ᵥ productVector y v =
      (star x ⬝ᵥ y) * (star u ⬝ᵥ v) := by
  simp only [dotProduct, Fintype.sum_prod_type, productVector, Pi.star_apply,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma choi_eq_amplify {a b : ℕ} (F : Mat a → Mat b) :
    choi F = amplify F a (pure (omega a)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  change F (Matrix.single i j 1) u v = F (fun p q => pure (omega a) (i,p) (j,q)) u v
  congr 2
  ext p q
  simp [pure, omega, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and]
  split_ifs <;> simp_all

lemma cp_choi_posSemidef {a b : ℕ} (F : Mat a → Mat b) (hF : CompletelyPositive F)
    (ha : 0 < a) : (choi F).PosSemidef := by
  rw [choi_eq_amplify]
  exact hF a ha _ (pure_posSemidef _)

lemma cp_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : CompletelyPositive F) (hG : CompletelyPositive G) :
    CompletelyPositive (G ∘ F) := by
  intro k hk X hX
  exact hG k hk _ (hF k hk X hX)

lemma eb_choi_separable {a b : ℕ} (F : Mat a → Mat b) (hF : EntanglementBreaking F)
    (ha : 0 < a) : separable (choi F) := by
  rw [choi_eq_amplify]
  exact hF.2 a ha _ (pure_posSemidef _)

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Kraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

lemma krausMap_add {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A B : Matrix a a ℂ) :
    krausMap Q (A + B) = krausMap Q A + krausMap Q B := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma krausMap_smul {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (c : ℂ) (A : Matrix a a ℂ) :
    krausMap Q (c • A) = c • krausMap Q A := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma krausMap_linear {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : IsComplexLinear (krausMap Q) :=
  ⟨krausMap_add Q, krausMap_smul Q⟩

lemma posSemidef_sum {r n : Type*} [Fintype r] (A : r → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef := by
  classical
  have hh : ∀ s : Finset r, (∑ i ∈ s, A i).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
    | @insert i s hi ih => simpa [Finset.sum_insert hi] using (h i).add ih
  exact hh Finset.univ

lemma krausMap_positive {r a b : Type*} [Fintype r] [Fintype a] [Finite b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    (krausMap Q A).PosSemidef := by
  exact posSemidef_sum _ (fun k => hA.mul_mul_conjTranspose_same (Q k))

lemma krausMap_entry {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (u v : b) :
    krausMap Q A u v = ∑ k, ∑ i, ∑ j, Q k u i * A i j * star (Q k v j) := by
  simp only [krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma amplify_kraus {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplify (krausMap Q) k X = krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X := by
  ext u v
  change krausMap Q (fun i j => X (u.1, i) (v.1, j)) u.2 v.2 =
    krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X u v
  erw [krausMap_entry, krausMap_entry]
  have hentry (r : r) (u : Fin k × Fin b) (v : Fin k × Fin a) :
      ((1 : Mat k) ⊗ₖ Q r) u v = if u.1 = v.1 then Q r u.2 v.2 else 0 := by
    change (if u.1 = v.1 then (1 : ℂ) else 0) * Q r u.2 v.2 = _
    split <;> simp_all
  simp only [hentry]
  simp [Fintype.sum_prod_type, apply_ite star, ite_mul, mul_ite]

lemma krausMap_cp {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : CompletelyPositive (krausMap Q) := by
  intro k hk X hX
  rw [amplify_kraus]
  exact krausMap_positive _ X hX

lemma krausMap_single {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (i j : Fin a) (u v : Fin b) :
    krausMap Q (Matrix.single i j 1) u v = ∑ k, Q k u i * star (Q k v j) := by
  simp [krausMap_entry, Matrix.single_apply, ite_and]

lemma krausMap_adjoint {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) :
    hsAdjoint (krausMap Q) = krausMap (fun k => (Q k)ᴴ) := by
  funext A
  ext i j
  change (∑ u, ∑ v, star (krausMap Q (Matrix.single i j 1) u v) * A u v) = _
  simp only [krausMap_single]
  simp only [krausMap_entry,
    star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext v; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_TensorKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma sum_kronecker {r a b c d : Type*} [Fintype r]
    (A : r → Matrix a b ℂ) (B : Matrix c d ℂ) :
    (∑ r, A r) ⊗ₖ B = ∑ r, A r ⊗ₖ B := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_mul]

lemma kronecker_sum {r a b c d : Type*} [Fintype r]
    (A : Matrix a b ℂ) (B : r → Matrix c d ℂ) :
    A ⊗ₖ (∑ r, B r) = ∑ r, A ⊗ₖ B r := by
  ext i j
  simp [Matrix.sum_apply, Finset.mul_sum]

lemma block_expansion {a c : ℕ} (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    X = ∑ i : Fin c, ∑ j : Fin c,
      (Matrix.of (fun a b => X (a, i) (b, j))) ⊗ₖ (Matrix.single i j 1) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma sum_four_comm {a b c d M : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [AddCommMonoid M] (f : a → b → c → d → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma tensorMap_kraus {r s : Type*} [Fintype r] [Fintype s] {a b c d : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (R : s → Matrix (Fin d) (Fin c) ℂ)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (krausMap Q) (krausMap R) X =
      krausMap (fun p : r × s => Q p.1 ⊗ₖ R p.2) X := by
  conv_rhs => arg 2; rw [block_expansion X]
  simp only [tensorMap, Matrix.kronecker, krausMap, Fintype.sum_prod_type, Matrix.conjTranspose_kronecker,
    Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
    sum_kronecker, kronecker_sum]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  exact sum_four_comm (fun (i j : Fin c) (k : r) (l : s) =>
    (Q k * Matrix.of (fun a b => X (a, i) (b, j)) * (Q k)ᴴ) ⊗ₖ
      (R l * Matrix.single i j 1 * (R l)ᴴ))

lemma krausMap_conjugate {r a b c d : Type*} [Fintype r] [Fintype a] [Fintype b]
    [Fintype c] (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (V : Matrix d b ℂ)
    (A : Matrix c c ℂ) :
    V * krausMap Q (U * A * Uᴴ) * Vᴴ =
      krausMap (fun k => V * Q k * U) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_postconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (V : Matrix c b ℂ) (A : Matrix a a ℂ) :
    V * krausMap Q A * Vᴴ = krausMap (fun k => V * Q k) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_preconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype c]
    (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (A : Matrix c c ℂ) :
    krausMap Q (U * A * Uᴴ) = krausMap (fun k => Q k * U) A := by
  simp only [krausMap, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma kronecker_transpose {a b c d : Type*} (A : Matrix a b ℂ) (B : Matrix c d ℂ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

lemma tensorMap_output_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, (F A)ᵀ = F A) (hG : ∀ A, (G A)ᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    (tensorMap F G X)ᵀ = tensorMap F G X := by
  simp only [tensorMap, Matrix.kronecker, Matrix.transpose_sum, kronecker_transpose, hG]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  erw [hF]

lemma tensorMap_input_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, F Aᵀ = F A) (hG : ∀ A, G Aᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap F G Xᵀ = tensorMap F G X := by
  unfold tensorMap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (fun a b => Xᵀ (a, j) (b, i)) =
      (Matrix.of (fun a b => X (a, i) (b, j)))ᵀ := rfl
  rw [hb, hF]
  have hg : G (Matrix.single j i 1) = G (Matrix.single i j 1) := by
    have ht : (Matrix.single i j (1 : ℂ))ᵀ = Matrix.single j i 1 := by
      simp only [Matrix.transpose_single]
    rw [← ht, hG]
  rw [hg]
  rfl

lemma hsAdjoint_output_transpose {a b : ℕ} (F : Mat a → Mat b)
    (h : ∀ A, F Aᵀ = F A) (Y : Mat b) :
    (hsAdjoint F Y)ᵀ = hsAdjoint F Y := by
  ext i j
  change (∑ u, ∑ v, star (F (Matrix.single j i 1) u v) * Y u v) = _
  have he : F (Matrix.single j i 1) = F (Matrix.single i j 1) := by
    rw [← Matrix.transpose_single, h]
  rw [he]
  rfl

lemma symmetricIsometry_real : symmetricIsometryᴴ = symmetricIsometryᵀ := by
  ext i j
  simp [symmetricIsometry, Matrix.conjTranspose_apply, apply_ite star]

lemma exteriorIsometry_real : exteriorIsometryᴴ = exteriorIsometryᵀ := by
  ext i j
  simp [exteriorIsometry, Matrix.conjTranspose_apply]

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

lemma real_compression_transpose {a b : Type*} [Fintype a]
    (V : Matrix a b ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (Vᴴ * A * V)ᵀ = Vᴴ * Aᵀ * V := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma real_embedding_transpose {a b : Type*} [Fintype a]
    (V : Matrix b a ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (V * A * Vᴴ)ᵀ = V * Aᵀ * Vᴴ := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Veronese
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma veronese_dot (u : Fin 10 → ℂ) (x : Fin 4 → ℂ) :
    star u ⬝ᵥ veronese x = quadraticEval (veroneseCoeffs u) x := by
  rw [quadraticEval, ← Equiv.sum_comp symmetricEquiv]
  simp only [veroneseCoeffs, Equiv.symm_apply_apply, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change star (u i) * veronese x i = star (u i) *
    (if (symmetricPairs i).1 = (symmetricPairs i).2 then 1 else (Real.sqrt 2 : ℂ)) *
      x (symmetricPairs i).1 * x (symmetricPairs i).2
  simp only [veronese]
  ring

lemma veroneseCoeffs_ne {u : Fin 10 → ℂ} (hu : u ≠ 0) : veroneseCoeffs u ≠ 0 := by
  intro hh
  apply hu
  ext i
  have hi := congrFun hh (symmetricEquiv i)
  simp only [veroneseCoeffs, Equiv.symm_apply_apply, Pi.zero_apply] at hi
  have hn : (if (symmetricEquiv i).val.1 = (symmetricEquiv i).val.2 then (1:ℂ)
    else (Real.sqrt 2 : ℂ)) ≠ 0 := by split_ifs <;> simp_all
  have : star (u i) = 0 := (mul_eq_zero.mp hi).resolve_right hn
  simpa only [star_eq_zero, Pi.zero_apply] using this

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pencilKraus_real (r : Fin 6) (i j : Fin 4) : star (pencilKraus r i j) = pencilKraus r i j := by
  simp [pencilKraus, blocks]

lemma pencilMap_kraus : pencilMap = krausMap pencilKraus := by
  funext A
  ext u v
  simp only [pencilMap, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, krausMap_entry,
    pencilKraus_real]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [pencilKraus]
  ring

lemma pencilMap_input_transpose (A : Mat 4) : pencilMap Aᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

lemma pencilMap_output_transpose (A : Mat 4) : (pencilMap A)ᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma exteriorMap_kraus : exteriorMap = krausMap exteriorKraus := by
  funext A
  unfold exteriorMap
  rw [pencilMap_kraus, tensorMap_kraus]
  have h := krausMap_conjugate (fun p : Fin 6 × Fin 6 => pencilKraus p.1 ⊗ₖ pencilKraus p.2)
    symmetricIsometry exteriorIsometryᴴ A
  unfold exteriorKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma exteriorMap_output_transpose (A : Mat 10) : (exteriorMap A)ᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [real_compression_transpose _ exteriorIsometry_real]
  rw [tensorMap_output_transpose _ _ pencilMap_output_transpose pencilMap_output_transpose]

lemma exteriorMap_input_transpose (A : Mat 10) : exteriorMap Aᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [← real_embedding_transpose _ symmetricIsometry_real]
  rw [tensorMap_input_transpose _ _ pencilMap_input_transpose pencilMap_input_transpose]

lemma complementaryMap_kraus : complementaryMap = krausMap complementaryKraus := by
  funext A
  unfold complementaryMap
  rw [exteriorMap_output_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma complementaryMap_input_transpose (A : Mat 10) : complementaryMap Aᵀ = complementaryMap A := by
  simp only [complementaryMap, exteriorMap_input_transpose]

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiTwo_kraus : phiTwo = krausMap phiTwoKraus := by
  funext A
  unfold phiTwo
  rw [complementaryMap_kraus, krausMap_adjoint]
  have h := krausMap_preconjugate (fun k => (complementaryKraus k)ᴴ) firstSixᴴ A
  unfold phiTwoKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

lemma phiTwo_output_transpose (A : Mat 10) : (phiTwo A)ᵀ = phiTwo A :=
  hsAdjoint_output_transpose _ complementaryMap_input_transpose _

lemma phiOne_ppt : PPT phiOne := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiOne_kraus]; exact krausMap_linear _
  · rw [phiOne_kraus]; exact krausMap_cp _
  · simp only [phiOne_output_transpose]
    rw [phiOne_kraus]; exact krausMap_cp _

lemma phiTwo_ppt : PPT phiTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiTwo_kraus]; exact krausMap_linear _
  · rw [phiTwo_kraus]; exact krausMap_cp _
  · simp only [phiTwo_output_transpose]
    rw [phiTwo_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ExteriorEvaluation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma compositeChoi_posSemidef : compositeChoi.PosSemidef := by
  exact cp_choi_posSemidef _ (cp_comp _ _ phiOne_ppt.2.1 phiTwo_ppt.2.1) (by decide)

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_FamilyGeometry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma no_two_zero_cover (p q : Fin 20 → ℂ)
    (hp : (Finset.univ.filter (fun k => p k = 0)).card ≤ 9)
    (hq : (Finset.univ.filter (fun k => q k = 0)).card ≤ 9)
    (h : ∀ k, p k = 0 ∨ q k = 0) : False := by
  classical
  have hs : Finset.univ ⊆ (Finset.univ.filter (fun k => p k = 0)) ∪
      (Finset.univ.filter (fun k => q k = 0)) := by
    intro k hk
    simpa using h k
  have hh := Finset.card_le_card hs
  have hu := Finset.card_union_le (Finset.univ.filter (fun k => p k = 0))
    (Finset.univ.filter (fun k => q k = 0))
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  omega

lemma productfree_of_kernel_family (X : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ)
    (hX : X.IsHermitian) (f : Fin 20 → (Fin 10 → ℂ))
    (hpos : ∀ u : Fin 10 → ℂ, u ≠ 0 →
      (Finset.univ.filter (fun k => star u ⬝ᵥ f k = 0)).card ≤ 9)
    (hker : ∀ k, X *ᵥ productVector (f k) (f k) = 0) :
    ∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      X *ᵥ w = productVector u v → u = 0 ∨ v = 0 := by
  intro u v w hw
  by_cases hu : u = 0
  · exact Or.inl hu
  by_cases hv : v = 0
  · exact Or.inr hv
  exfalso
  apply no_two_zero_cover (fun k => star u ⬝ᵥ f k) (fun k => star v ⬝ᵥ f k)
    (hpos u hu) (hpos v hv)
  intro k
  apply mul_eq_zero.mp
  rw [← product_dot, ← hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    hX.eq, hker, dotProduct_zero]

lemma kronecker_mul_product {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    (A ⊗ₖ B) *ᵥ productVector u v = productVector (A *ᵥ u) (B *ᵥ v) := by
  ext ⟨i,j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, productVector,
    Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma kronecker_product_dot {a b : ℕ} (A : Mat a) (B : Mat b)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ ((A ⊗ₖ B) *ᵥ productVector u v) =
      (star u ⬝ᵥ (A *ᵥ u)) * (star v ⬝ᵥ (B *ᵥ v)) := by
  rw [kronecker_mul_product, product_dot]

lemma psd_summand_kernel {r n : Type*} [Fintype r] [Fintype n]
    (A : r → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (v : n → ℂ)
    (hv : (∑ i, A i) *ᵥ v = 0) (i : r) : A i *ᵥ v = 0 := by
  have hs : ∑ j, star v ⬝ᵥ (A j *ᵥ v) = 0 := by
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hv, dotProduct_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset r)) => (hA j).dotProduct_mulVec_nonneg v)).mp hs i
      (Finset.mem_univ i)
  exact ((hA i).dotProduct_mulVec_zero_iff _).mp hi

lemma matrix_nonzero_row {n : ℕ} {A : Mat n} (hA : A ≠ 0) :
    ∃ i : Fin n, star (A i) ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hA
  ext i j
  have hi := congrFun (hh i) j
  simpa only [Pi.star_apply, Pi.zero_apply, star_eq_zero, Matrix.zero_apply] using hi

lemma nonseparable_of_kernel_family (X : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ)
    (hne : X ≠ 0) (f : Fin 20 → (Fin 10 → ℂ))
    (hpos : ∀ u : Fin 10 → ℂ, u ≠ 0 →
      (Finset.univ.filter (fun k => star u ⬝ᵥ f k = 0)).card ≤ 9)
    (hker : ∀ k, X *ᵥ productVector (f k) (f k) = 0) : ¬ separable X := by
  intro hsep
  obtain ⟨r, A, B, hAB, hsum⟩ := hsep
  have hi (i : Fin r) : A i = 0 ∨ B i = 0 := by
    by_cases hA : A i = 0
    · exact Or.inl hA
    by_cases hB : B i = 0
    · exact Or.inr hB
    exfalso
    obtain ⟨a, ha⟩ := matrix_nonzero_row hA
    obtain ⟨b, hb⟩ := matrix_nonzero_row hB
    apply no_two_zero_cover
      (fun k => star (star (A i a)) ⬝ᵥ f k) (fun k => star (star (B i b)) ⬝ᵥ f k)
      (hpos _ ha) (hpos _ hb)
    intro k
    have hk : (A i ⊗ₖ B i) *ᵥ productVector (f k) (f k) = 0 := by
      apply psd_summand_kernel (fun j => A j ⊗ₖ B j)
        (fun j => (hAB j).1.kronecker (hAB j).2) _ _ i
      simpa only [Matrix.kronecker] using hsum ▸ hker k
    have hd : (star (f k) ⬝ᵥ (A i *ᵥ f k)) * (star (f k) ⬝ᵥ (B i *ᵥ f k)) = 0 := by
      rw [← kronecker_product_dot, hk, dotProduct_zero]
    rcases mul_eq_zero.mp hd with h | h
    · left
      have hz := ((hAB i).1.dotProduct_mulVec_zero_iff _).mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz a
    · right
      have hz := ((hAB i).2.dotProduct_mulVec_zero_iff _).mp h
      simpa only [star_star, Matrix.mulVec, Pi.zero_apply] using congrFun hz b
  apply hne
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i hi'
  rcases hi i with h | h <;> simp [h, Matrix.kronecker]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilPoints
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

lemma cofactor_last_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin 3 → R) :
    f (cofactorKernel (Fin.cons 1 t) 3) =
      cofactorKernel (Fin.cons 1 (fun j => f (t j))) 3 := by
  rw [cofactor_chart_last, cofactor_chart_last, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_intCast, low_map]

lemma rank_embedding {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    (pencilR (Fin.cons 1 (fun j => σ (alpha j)))).rank < 4 := by
  apply rank_lt_of_kernel _ (cofactorKernel (Fin.cons 1 (fun j => σ (alpha j))))
  · intro h
    have hz := congrFun h 3
    have hc := cofactor_last_map σ.toRingHom alpha
    have hne : σ.toRingHom (cofactorKernel (Fin.cons 1 alpha) 3) ≠ 0 :=
      (map_ne_zero σ.toRingHom).mpr cofactor_alpha_last_ne
    exact hne (hc.trans hz)
  · exact cofactorKernel_eq_zero _ (minors_embedding σ)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_TwentyDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma rank_points (k : Fin 20) : (pencil (chart (points k))).rank < 4 :=
  rank_embedding (embeddingsC k)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma veronese_family_general_position (u : Fin 10 → ℂ) (hu : u ≠ 0) :
    (Finset.univ.filter (fun k : Fin 20 =>
      star u ⬝ᵥ veronese (chart (Border.points k)) = 0)).card ≤ 9 := by
  simp only [veronese_dot]
  exact Border.quadratic_zero_bound _ (veroneseCoeffs_ne hu)

lemma compositeChoi_productfree :
    ∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      compositeChoi *ᵥ w = productVector u v → u = 0 ∨ v = 0 := by
  exact productfree_of_kernel_family _ compositeChoi_posSemidef.isHermitian
    (fun k => veronese (chart (Border.points k))) veronese_family_general_position
    (fun k => compositeChoi_kernel_rank (Border.rank_points k))

lemma compositeChoi_not_separable : ¬ separable compositeChoi := by
  exact nonseparable_of_kernel_family _ compositeChoi_ne
    (fun k => veronese (chart (Border.points k))) veronese_family_general_position
    (fun k => compositeChoi_kernel_rank (Border.rank_points k))


theorem exactDimensionTenPair : ExactDimensionTenPair := by
  refine ⟨phiOne_ppt, phiTwo_ppt, compositeChoi_ne, compositeChoi_productfree, ?_⟩
  intro h
  exact compositeChoi_not_separable (eb_choi_separable _ h (by decide))

end DimensionTen

end
end


noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex
namespace DimensionTen





theorem main_pair_oai :
    ∃ Φ₁ Φ₂ : Mat 10 → Mat 10,
      Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ PPT Φ₁ ∧ PPT Φ₂ ∧
      (let Z := choi (Φ₂ ∘ Φ₁)
       Z ≠ 0 ∧
       (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
         Z *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
       ¬ EntanglementBreaking (Φ₂ ∘ Φ₁)) := by
  rcases exactDimensionTenPair with ⟨h₁, h₂, hn, hp, he⟩
  exact ⟨phiOne, phiTwo, rfl, rfl, h₁, h₂, hn, hp, he⟩

end DimensionTen
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.main_pair_oai := @OAI.DimensionTen.main_pair_oai
