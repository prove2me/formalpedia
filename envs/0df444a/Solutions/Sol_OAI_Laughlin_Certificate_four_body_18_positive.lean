-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_18_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:20:01.358599+00:00
-- url     : https://prove2.me/submissions/fbc249d8-b49a-4f47-9c5c-059f645aee68

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_18

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_18 : GramCompute.quadruples 18 = [(0,1,2,16), (0,1,3,15), (0,1,4,14), (0,1,5,13), (0,1,6,12), (0,1,7,11), (0,1,8,10), (0,2,3,14), (0,2,4,13), (0,2,5,12), (0,2,6,11), (0,2,7,10), (0,2,8,9), (0,3,4,12), (0,3,5,11), (0,3,6,10), (0,3,7,9), (0,4,5,10), (0,4,6,9), (0,4,7,8), (0,5,6,8), (1,2,3,13), (1,2,4,12), (1,2,5,11), (1,2,6,10), (1,2,7,9), (1,3,4,11), (1,3,5,10), (1,3,6,9), (1,3,7,8), (1,4,5,9), (1,4,6,8), (1,5,6,7), (2,3,4,10), (2,3,5,9), (2,3,6,8), (2,4,5,8), (2,4,6,7), (3,4,5,7)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_1_1 : GramCompute.ZFast 18 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_3 : GramCompute.ZFast 18 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_5 : GramCompute.ZFast 18 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_7 : GramCompute.ZFast 18 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_9 : GramCompute.ZFast 18 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_11 : GramCompute.ZFast 18 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_13 : GramCompute.ZFast 18 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_15 : GramCompute.ZFast 18 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_1_17 : GramCompute.ZFast 18 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_3_3 : GramCompute.ZFast 18 3 3 = (7846046208000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_5 : GramCompute.ZFast 18 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_7 : GramCompute.ZFast 18 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_9 : GramCompute.ZFast 18 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_11 : GramCompute.ZFast 18 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_13 : GramCompute.ZFast 18 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_15 : GramCompute.ZFast 18 3 15 = (-858161304000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_3_17 : GramCompute.ZFast 18 3 17 = (16672848192000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_5_5 : GramCompute.ZFast 18 5 5 = (747242496000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_7 : GramCompute.ZFast 18 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_9 : GramCompute.ZFast 18 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_11 : GramCompute.ZFast 18 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_13 : GramCompute.ZFast 18 5 13 = (-140107968000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_15 : GramCompute.ZFast 18 5 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_5_17 : GramCompute.ZFast 18 5 17 = (11115232128000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_7_7 : GramCompute.ZFast 18 7 7 = (201180672000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_7_9 : GramCompute.ZFast 18 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_7_11 : GramCompute.ZFast 18 7 11 = (-47151720000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_7_13 : GramCompute.ZFast 18 7 13 = (-163459296000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_7_15 : GramCompute.ZFast 18 7 15 = (643620978000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_7_17 : GramCompute.ZFast 18 7 17 = (4168212048000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_9_9 : GramCompute.ZFast 18 9 9 = (98761420800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_11 : GramCompute.ZFast 18 9 11 = (-113164128000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_13 : GramCompute.ZFast 18 9 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_15 : GramCompute.ZFast 18 9 15 = (367783416000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_17 : GramCompute.ZFast 18 9 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_11_11 : GramCompute.ZFast 18 11 11 = (149313780000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_13 : GramCompute.ZFast 18 11 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_15 : GramCompute.ZFast 18 11 15 = (-421418497500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_17 : GramCompute.ZFast 18 11 17 = (-1736755020000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_13_13 : GramCompute.ZFast 18 13 13 = (329837508000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_13_15 : GramCompute.ZFast 18 13 15 = (-1195296102000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_13_17 : GramCompute.ZFast 18 13 17 = (-2084106024000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram15Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_15_15 : GramCompute.ZFast 18 15 15 = (6169949911125 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_15_17 : GramCompute.ZFast 18 15 17 = (-1823592771000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram171718
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_17_17 : GramCompute.ZFast 18 17 17 = (354298024080000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MatrixCompute
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_0_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_0_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 0 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_1_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_1_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 1 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_2_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_2_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 2 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 2 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_3_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_3_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 3 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 3 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_4_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_4_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 4 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 4 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_5_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_5_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 5 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 5 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_6_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_6_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 6 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 6 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_7_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_7_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 7 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 7 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL08Batch18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_18_8_0 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 0 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_1 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 1 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_2 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 2 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_3 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 3 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_4 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 4 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_5 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 5 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_6 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 6 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_7 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 7 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_18_8_8 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 8 8 =
    (lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose) 8 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_RationalPSD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem rational_ldl_positive {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : A = L * Matrix.diagonal d * L.transpose)
    (hd : ∀ i, 0 ≤ d i) : (A.map (Rat.castHom ℝ)).PosSemidef := by
  rw [h, Matrix.map_mul, Matrix.map_mul]
  have hdiag : (Matrix.diagonal d).map (Rat.castHom ℝ) =
      Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have htrans : L.transpose.map (Rat.castHom ℝ) =
      (L.map (Rat.castHom ℝ)).conjTranspose := by
    ext i j
    simp
  rw [hdiag, htrans]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℝ) ≤ (d i : ℝ)
  exact_mod_cast hd i

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_eq_gramCompute (D r s : ℕ) : Z D r s = GramCompute.ZFast D r s := by
  exact Z_eq_fast D r s

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_symm (D r s : ℕ) : Z D r s = Z D s r := by
  unfold Z
  congr 1
  apply List.map_congr_left
  intro A hA
  dsimp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_18_1_1 : Z 18 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_1

theorem source_gram_18_1_3 : Z 18 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_3

theorem source_gram_18_1_5 : Z 18 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_5

theorem source_gram_18_1_7 : Z 18 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_7

theorem source_gram_18_1_9 : Z 18 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_9

theorem source_gram_18_1_11 : Z 18 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_11

theorem source_gram_18_1_13 : Z 18 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_13

theorem source_gram_18_1_15 : Z 18 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_15

theorem source_gram_18_1_17 : Z 18 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_17

theorem source_gram_18_3_3 : Z 18 3 3 = (7846046208000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_3

theorem source_gram_18_3_5 : Z 18 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_5

theorem source_gram_18_3_7 : Z 18 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_7

theorem source_gram_18_3_9 : Z 18 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_9

theorem source_gram_18_3_11 : Z 18 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_11

theorem source_gram_18_3_13 : Z 18 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_13

theorem source_gram_18_3_15 : Z 18 3 15 = (-858161304000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_15

theorem source_gram_18_3_17 : Z 18 3 17 = (16672848192000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_17

theorem source_gram_18_5_5 : Z 18 5 5 = (747242496000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_5

theorem source_gram_18_5_7 : Z 18 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_7

theorem source_gram_18_5_9 : Z 18 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_9

theorem source_gram_18_5_11 : Z 18 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_11

theorem source_gram_18_5_13 : Z 18 5 13 = (-140107968000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_13

theorem source_gram_18_5_15 : Z 18 5 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_15

theorem source_gram_18_5_17 : Z 18 5 17 = (11115232128000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_17

theorem source_gram_18_7_7 : Z 18 7 7 = (201180672000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_7

theorem source_gram_18_7_9 : Z 18 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_9

theorem source_gram_18_7_11 : Z 18 7 11 = (-47151720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_11

theorem source_gram_18_7_13 : Z 18 7 13 = (-163459296000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_13

theorem source_gram_18_7_15 : Z 18 7 15 = (643620978000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_15

theorem source_gram_18_7_17 : Z 18 7 17 = (4168212048000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_17

theorem source_gram_18_9_9 : Z 18 9 9 = (98761420800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_9

theorem source_gram_18_9_11 : Z 18 9 11 = (-113164128000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_11

theorem source_gram_18_9_13 : Z 18 9 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_13

theorem source_gram_18_9_15 : Z 18 9 15 = (367783416000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_15

theorem source_gram_18_9_17 : Z 18 9 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_17

theorem source_gram_18_11_11 : Z 18 11 11 = (149313780000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_11

theorem source_gram_18_11_13 : Z 18 11 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_13

theorem source_gram_18_11_15 : Z 18 11 15 = (-421418497500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_15

theorem source_gram_18_11_17 : Z 18 11 17 = (-1736755020000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_17

theorem source_gram_18_13_13 : Z 18 13 13 = (329837508000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_13

theorem source_gram_18_13_15 : Z 18 13 15 = (-1195296102000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_15

theorem source_gram_18_13_17 : Z 18 13 17 = (-2084106024000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_17

theorem source_gram_18_15_15 : Z 18 15 15 = (6169949911125 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_15_15

theorem source_gram_18_15_17 : Z 18 15 17 = (-1823592771000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_15_17

theorem source_gram_18_17_17 : Z 18 17 17 = (354298024080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_17_17

theorem source_gram_18_3_1 : Z 18 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_3

theorem source_gram_18_5_1 : Z 18 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_5

theorem source_gram_18_5_3 : Z 18 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_5

theorem source_gram_18_7_1 : Z 18 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_7

theorem source_gram_18_7_3 : Z 18 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_7

theorem source_gram_18_7_5 : Z 18 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_7

theorem source_gram_18_9_1 : Z 18 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_9

theorem source_gram_18_9_3 : Z 18 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_9

theorem source_gram_18_9_5 : Z 18 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_9

theorem source_gram_18_9_7 : Z 18 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_9

theorem source_gram_18_11_1 : Z 18 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_11

theorem source_gram_18_11_3 : Z 18 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_11

theorem source_gram_18_11_5 : Z 18 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_11

theorem source_gram_18_11_7 : Z 18 11 7 = (-47151720000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_11

theorem source_gram_18_11_9 : Z 18 11 9 = (-113164128000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_11

theorem source_gram_18_13_1 : Z 18 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_13

theorem source_gram_18_13_3 : Z 18 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_13

theorem source_gram_18_13_5 : Z 18 13 5 = (-140107968000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_13

theorem source_gram_18_13_7 : Z 18 13 7 = (-163459296000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_13

theorem source_gram_18_13_9 : Z 18 13 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_13

theorem source_gram_18_13_11 : Z 18 13 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_13

theorem source_gram_18_15_1 : Z 18 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_15

theorem source_gram_18_15_3 : Z 18 15 3 = (-858161304000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_15

theorem source_gram_18_15_5 : Z 18 15 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_15

theorem source_gram_18_15_7 : Z 18 15 7 = (643620978000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_15

theorem source_gram_18_15_9 : Z 18 15 9 = (367783416000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_15

theorem source_gram_18_15_11 : Z 18 15 11 = (-421418497500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_15

theorem source_gram_18_15_13 : Z 18 15 13 = (-1195296102000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_13_15

theorem source_gram_18_17_1 : Z 18 17 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_17

theorem source_gram_18_17_3 : Z 18 17 3 = (16672848192000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_17

theorem source_gram_18_17_5 : Z 18 17 5 = (11115232128000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_17

theorem source_gram_18_17_7 : Z 18 17 7 = (4168212048000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_17

theorem source_gram_18_17_9 : Z 18 17 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_17

theorem source_gram_18_17_11 : Z 18 17 11 = (-1736755020000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_17

theorem source_gram_18_17_13 : Z 18 17 13 = (-2084106024000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_13_17

theorem source_gram_18_17_15 : Z 18 17 15 = (-1823592771000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_15_17

theorem gram_18 : gramRational 18 = candidateZ_18 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_18_1_1
  · exact source_gram_18_1_3
  · exact source_gram_18_1_5
  · exact source_gram_18_1_7
  · exact source_gram_18_1_9
  · exact source_gram_18_1_11
  · exact source_gram_18_1_13
  · exact source_gram_18_1_15
  · exact source_gram_18_1_17
  · exact source_gram_18_3_1
  · exact source_gram_18_3_3
  · exact source_gram_18_3_5
  · exact source_gram_18_3_7
  · exact source_gram_18_3_9
  · exact source_gram_18_3_11
  · exact source_gram_18_3_13
  · exact source_gram_18_3_15
  · exact source_gram_18_3_17
  · exact source_gram_18_5_1
  · exact source_gram_18_5_3
  · exact source_gram_18_5_5
  · exact source_gram_18_5_7
  · exact source_gram_18_5_9
  · exact source_gram_18_5_11
  · exact source_gram_18_5_13
  · exact source_gram_18_5_15
  · exact source_gram_18_5_17
  · exact source_gram_18_7_1
  · exact source_gram_18_7_3
  · exact source_gram_18_7_5
  · exact source_gram_18_7_7
  · exact source_gram_18_7_9
  · exact source_gram_18_7_11
  · exact source_gram_18_7_13
  · exact source_gram_18_7_15
  · exact source_gram_18_7_17
  · exact source_gram_18_9_1
  · exact source_gram_18_9_3
  · exact source_gram_18_9_5
  · exact source_gram_18_9_7
  · exact source_gram_18_9_9
  · exact source_gram_18_9_11
  · exact source_gram_18_9_13
  · exact source_gram_18_9_15
  · exact source_gram_18_9_17
  · exact source_gram_18_11_1
  · exact source_gram_18_11_3
  · exact source_gram_18_11_5
  · exact source_gram_18_11_7
  · exact source_gram_18_11_9
  · exact source_gram_18_11_11
  · exact source_gram_18_11_13
  · exact source_gram_18_11_15
  · exact source_gram_18_11_17
  · exact source_gram_18_13_1
  · exact source_gram_18_13_3
  · exact source_gram_18_13_5
  · exact source_gram_18_13_7
  · exact source_gram_18_13_9
  · exact source_gram_18_13_11
  · exact source_gram_18_13_13
  · exact source_gram_18_13_15
  · exact source_gram_18_13_17
  · exact source_gram_18_15_1
  · exact source_gram_18_15_3
  · exact source_gram_18_15_5
  · exact source_gram_18_15_7
  · exact source_gram_18_15_9
  · exact source_gram_18_15_11
  · exact source_gram_18_15_13
  · exact source_gram_18_15_15
  · exact source_gram_18_15_17
  · exact source_gram_18_17_1
  · exact source_gram_18_17_3
  · exact source_gram_18_17_5
  · exact source_gram_18_17_7
  · exact source_gram_18_17_9
  · exact source_gram_18_17_11
  · exact source_gram_18_17_13
  · exact source_gram_18_17_15
  · exact source_gram_18_17_17

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_18 : MatrixCompute.compressed 18 candidateY_18 candidateZ_18 =
    lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_18_0_0
  · exact computeLDL_18_0_1
  · exact computeLDL_18_0_2
  · exact computeLDL_18_0_3
  · exact computeLDL_18_0_4
  · exact computeLDL_18_0_5
  · exact computeLDL_18_0_6
  · exact computeLDL_18_0_7
  · exact computeLDL_18_0_8
  · exact computeLDL_18_1_0
  · exact computeLDL_18_1_1
  · exact computeLDL_18_1_2
  · exact computeLDL_18_1_3
  · exact computeLDL_18_1_4
  · exact computeLDL_18_1_5
  · exact computeLDL_18_1_6
  · exact computeLDL_18_1_7
  · exact computeLDL_18_1_8
  · exact computeLDL_18_2_0
  · exact computeLDL_18_2_1
  · exact computeLDL_18_2_2
  · exact computeLDL_18_2_3
  · exact computeLDL_18_2_4
  · exact computeLDL_18_2_5
  · exact computeLDL_18_2_6
  · exact computeLDL_18_2_7
  · exact computeLDL_18_2_8
  · exact computeLDL_18_3_0
  · exact computeLDL_18_3_1
  · exact computeLDL_18_3_2
  · exact computeLDL_18_3_3
  · exact computeLDL_18_3_4
  · exact computeLDL_18_3_5
  · exact computeLDL_18_3_6
  · exact computeLDL_18_3_7
  · exact computeLDL_18_3_8
  · exact computeLDL_18_4_0
  · exact computeLDL_18_4_1
  · exact computeLDL_18_4_2
  · exact computeLDL_18_4_3
  · exact computeLDL_18_4_4
  · exact computeLDL_18_4_5
  · exact computeLDL_18_4_6
  · exact computeLDL_18_4_7
  · exact computeLDL_18_4_8
  · exact computeLDL_18_5_0
  · exact computeLDL_18_5_1
  · exact computeLDL_18_5_2
  · exact computeLDL_18_5_3
  · exact computeLDL_18_5_4
  · exact computeLDL_18_5_5
  · exact computeLDL_18_5_6
  · exact computeLDL_18_5_7
  · exact computeLDL_18_5_8
  · exact computeLDL_18_6_0
  · exact computeLDL_18_6_1
  · exact computeLDL_18_6_2
  · exact computeLDL_18_6_3
  · exact computeLDL_18_6_4
  · exact computeLDL_18_6_5
  · exact computeLDL_18_6_6
  · exact computeLDL_18_6_7
  · exact computeLDL_18_6_8
  · exact computeLDL_18_7_0
  · exact computeLDL_18_7_1
  · exact computeLDL_18_7_2
  · exact computeLDL_18_7_3
  · exact computeLDL_18_7_4
  · exact computeLDL_18_7_5
  · exact computeLDL_18_7_6
  · exact computeLDL_18_7_7
  · exact computeLDL_18_7_8
  · exact computeLDL_18_8_0
  · exact computeLDL_18_8_1
  · exact computeLDL_18_8_2
  · exact computeLDL_18_8_3
  · exact computeLDL_18_8_4
  · exact computeLDL_18_8_5
  · exact computeLDL_18_8_6
  · exact computeLDL_18_8_7
  · exact computeLDL_18_8_8

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_18 : compressedRational 18 =
    lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose := by
  rw [compressedRational_eq_compute, error_18, gram_18]
  exact candidateLDL_18

theorem four_body_18_positive_oai :
    ((compressedRational 18).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_18 pivots_18 ldl_18
  intro i
  fin_cases i <;> norm_num [pivots_18]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_18_positive_oai := @OAI.Laughlin.Certificate.four_body_18_positive_oai
