-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_12_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:31:16.242348+00:00
-- url     : https://prove2.me/submissions/ea9777d8-3c2c-4b85-b963-7c8939aa65c6

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_12_5_5_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_0_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_0_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 0 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_1_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_1_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_12_s50_oai : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 =
    lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_12_0_0
  · exact computeLDL_12_0_1
  · exact computeLDL_12_0_2
  · exact computeLDL_12_0_3
  · exact computeLDL_12_0_4
  · exact computeLDL_12_0_5
  · exact computeLDL_12_1_0
  · exact computeLDL_12_1_1
  · exact computeLDL_12_1_2
  · exact computeLDL_12_1_3
  · exact computeLDL_12_1_4
  · exact computeLDL_12_1_5_s50
  · exact computeLDL_12_2_0_s50
  · exact computeLDL_12_2_1_s50
  · exact computeLDL_12_2_2_s50
  · exact computeLDL_12_2_3_s50
  · exact computeLDL_12_2_4_s50
  · exact computeLDL_12_2_5_s50
  · exact computeLDL_12_3_0_s50
  · exact computeLDL_12_3_1_s50
  · exact computeLDL_12_3_2_s50
  · exact computeLDL_12_3_3_s50
  · exact computeLDL_12_3_4_s50
  · exact computeLDL_12_3_5_s50
  · exact computeLDL_12_4_0_s50
  · exact computeLDL_12_4_1_s50
  · exact computeLDL_12_4_2_s50
  · exact computeLDL_12_4_3_s50
  · exact computeLDL_12_4_4_s50
  · exact computeLDL_12_4_5_s50
  · exact computeLDL_12_5_0_s50
  · exact computeLDL_12_5_1_s50
  · exact computeLDL_12_5_2_s50
  · exact computeLDL_12_5_3_s50
  · exact computeLDL_12_5_4_s50
  · exact computeLDL_12_5_5_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_12_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_12_s50_oai
