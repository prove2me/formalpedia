-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_14_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:32:35.154909+00:00
-- url     : https://prove2.me/submissions/bdc286c0-2260-4d58-b38c-b891c0584a6e

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_1_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_14_6_6_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_0_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_0_6 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 0 6 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_14_1_0 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 0 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_1 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 1 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_2 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 2 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_3 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 3 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_4 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 4 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_14_1_5 : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 1 5 =
    (lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_14_s50_oai : MatrixCompute.compressed 14 candidateY_14 candidateZ_14 =
    lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_14_0_0
  · exact computeLDL_14_0_1
  · exact computeLDL_14_0_2
  · exact computeLDL_14_0_3
  · exact computeLDL_14_0_4
  · exact computeLDL_14_0_5
  · exact computeLDL_14_0_6
  · exact computeLDL_14_1_0
  · exact computeLDL_14_1_1
  · exact computeLDL_14_1_2
  · exact computeLDL_14_1_3
  · exact computeLDL_14_1_4
  · exact computeLDL_14_1_5
  · exact computeLDL_14_1_6_s50
  · exact computeLDL_14_2_0_s50
  · exact computeLDL_14_2_1_s50
  · exact computeLDL_14_2_2_s50
  · exact computeLDL_14_2_3_s50
  · exact computeLDL_14_2_4_s50
  · exact computeLDL_14_2_5_s50
  · exact computeLDL_14_2_6_s50
  · exact computeLDL_14_3_0_s50
  · exact computeLDL_14_3_1_s50
  · exact computeLDL_14_3_2_s50
  · exact computeLDL_14_3_3_s50
  · exact computeLDL_14_3_4_s50
  · exact computeLDL_14_3_5_s50
  · exact computeLDL_14_3_6_s50
  · exact computeLDL_14_4_0_s50
  · exact computeLDL_14_4_1_s50
  · exact computeLDL_14_4_2_s50
  · exact computeLDL_14_4_3_s50
  · exact computeLDL_14_4_4_s50
  · exact computeLDL_14_4_5_s50
  · exact computeLDL_14_4_6_s50
  · exact computeLDL_14_5_0_s50
  · exact computeLDL_14_5_1_s50
  · exact computeLDL_14_5_2_s50
  · exact computeLDL_14_5_3_s50
  · exact computeLDL_14_5_4_s50
  · exact computeLDL_14_5_5_s50
  · exact computeLDL_14_5_6_s50
  · exact computeLDL_14_6_0_s50
  · exact computeLDL_14_6_1_s50
  · exact computeLDL_14_6_2_s50
  · exact computeLDL_14_6_3_s50
  · exact computeLDL_14_6_4_s50
  · exact computeLDL_14_6_5_s50
  · exact computeLDL_14_6_6_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_14_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_14_s50_oai
