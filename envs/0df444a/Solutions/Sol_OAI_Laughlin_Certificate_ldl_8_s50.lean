-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_8_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:36:33.071578+00:00
-- url     : https://prove2.me/submissions/a47fc951-f19f-482c-b366-e33040b79587

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_error_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_8_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MatrixCompute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate.MatrixCompute

open scoped BigOperators

theorem middle_apply (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    middle D Y i j =
      (if i = j then ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D i else 0) -
        copyWeight D i * Y i j * copyWeight D j := by
  simp only [middle, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]

theorem compressed_apply (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    compressed D Y Z i j =
      ∑ k, (∑ l, Z i l *
        ((if l = k then ((if copyLabel l = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D l else 0) -
          copyWeight D l * Y l k * copyWeight D k)) * Z k j := by
  simp only [compressed, Matrix.mul_apply, middle_apply]

theorem ldl_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (i j : Fin n) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end Laughlin.Certificate.MatrixCompute

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDL08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8_0_0 : compressedRational 8 0 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 0 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_1 : compressedRational 8 0 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 1 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_2 : compressedRational 8 0 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 2 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_3 : compressedRational 8 0 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 3 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_0 : compressedRational 8 1 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 0 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_1 : compressedRational 8 1 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 1 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_2 : compressedRational 8 1 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 2 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_3 : compressedRational 8 1 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 3 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_0 : compressedRational 8 2 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 0 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_1 : compressedRational 8 2 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 1 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_2 : compressedRational 8 2 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 2 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_3 : compressedRational 8 2 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 3 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_0 : compressedRational 8 3 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 0 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_1 : compressedRational 8 3 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 1 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_2 : compressedRational 8 3 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 2 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_3 : compressedRational 8 3 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 3 := by
  rw [compressedRational_eq_compute, error_8_s50, gram_8_s50]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8_s50_oai : compressedRational 8 =
    lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact ldl_8_0_0
  · exact ldl_8_0_1
  · exact ldl_8_0_2
  · exact ldl_8_0_3
  · exact ldl_8_1_0
  · exact ldl_8_1_1
  · exact ldl_8_1_2
  · exact ldl_8_1_3
  · exact ldl_8_2_0
  · exact ldl_8_2_1
  · exact ldl_8_2_2
  · exact ldl_8_2_3
  · exact ldl_8_3_0
  · exact ldl_8_3_1
  · exact ldl_8_3_2
  · exact ldl_8_3_3

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_8_s50_oai := @OAI.Laughlin.Certificate.ldl_8_s50_oai
