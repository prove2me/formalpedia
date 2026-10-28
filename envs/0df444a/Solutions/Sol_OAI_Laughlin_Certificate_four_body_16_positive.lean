-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_16_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:08.805973+00:00
-- url     : https://prove2.me/submissions/9e40b961-22ef-4b5e-92e0-605d78470255

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_16

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_16 : GramCompute.quadruples 16 = [(0,1,2,14), (0,1,3,13), (0,1,4,12), (0,1,5,11), (0,1,6,10), (0,1,7,9), (0,2,3,12), (0,2,4,11), (0,2,5,10), (0,2,6,9), (0,2,7,8), (0,3,4,10), (0,3,5,9), (0,3,6,8), (0,4,5,8), (0,4,6,7), (1,2,3,11), (1,2,4,10), (1,2,5,9), (1,2,6,8), (1,3,4,9), (1,3,5,8), (1,3,6,7), (1,4,5,7), (2,3,4,8), (2,3,5,7), (2,4,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_1_1 : GramCompute.ZFast 16 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_3 : GramCompute.ZFast 16 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_5 : GramCompute.ZFast 16 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_7 : GramCompute.ZFast 16 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_9 : GramCompute.ZFast 16 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_11 : GramCompute.ZFast 16 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_13 : GramCompute.ZFast 16 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_1_15 : GramCompute.ZFast 16 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_3_3 : GramCompute.ZFast 16 3 3 = (37362124800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_5 : GramCompute.ZFast 16 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_7 : GramCompute.ZFast 16 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_9 : GramCompute.ZFast 16 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_11 : GramCompute.ZFast 16 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_13 : GramCompute.ZFast 16 3 13 = (-7005398400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_15 : GramCompute.ZFast 16 3 15 = (102162060000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_5_5 : GramCompute.ZFast 16 5 5 = (4790016000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_5_7 : GramCompute.ZFast 16 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_5_9 : GramCompute.ZFast 16 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_5_11 : GramCompute.ZFast 16 5 11 = (-1496880000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_5_13 : GramCompute.ZFast 16 5 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_5_15 : GramCompute.ZFast 16 5 15 = (61297236000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_7_7 : GramCompute.ZFast 16 7 7 = (1828915200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_9 : GramCompute.ZFast 16 7 9 = (-685843200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_11 : GramCompute.ZFast 16 7 11 = (-1571724000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_13 : GramCompute.ZFast 16 7 13 = (4086482400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_15 : GramCompute.ZFast 16 7 15 = (15324309000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_9_9 : GramCompute.ZFast 16 9 9 = (457228800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_11 : GramCompute.ZFast 16 9 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_13 : GramCompute.ZFast 16 9 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_15 : GramCompute.ZFast 16 9 15 = (-10216206000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_11_11 : GramCompute.ZFast 16 11 11 = (3555090000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_11_13 : GramCompute.ZFast 16 11 13 = (-8027019000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_11_15 : GramCompute.ZFast 16 11 15 = (-19155386250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_13_13 : GramCompute.ZFast 16 13 13 = (22183761600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_13_15 : GramCompute.ZFast 16 13 15 = (-19155386250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram151516
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_15_15 : GramCompute.ZFast 16 15 15 = (2584061605125/2 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_0_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_1_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_2_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_2_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 2 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_3_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_3_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 3 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_4_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_4_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 4 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_5_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_5_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 5 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_6_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_6_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 6 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_7_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_7_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 7 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 7 7 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_16_1_1 : Z 16 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_1

theorem source_gram_16_1_3 : Z 16 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_3

theorem source_gram_16_1_5 : Z 16 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_5

theorem source_gram_16_1_7 : Z 16 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_7

theorem source_gram_16_1_9 : Z 16 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_9

theorem source_gram_16_1_11 : Z 16 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_11

theorem source_gram_16_1_13 : Z 16 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_13

theorem source_gram_16_1_15 : Z 16 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_15

theorem source_gram_16_3_3 : Z 16 3 3 = (37362124800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_3

theorem source_gram_16_3_5 : Z 16 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_5

theorem source_gram_16_3_7 : Z 16 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_7

theorem source_gram_16_3_9 : Z 16 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_9

theorem source_gram_16_3_11 : Z 16 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_11

theorem source_gram_16_3_13 : Z 16 3 13 = (-7005398400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_13

theorem source_gram_16_3_15 : Z 16 3 15 = (102162060000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_15

theorem source_gram_16_5_5 : Z 16 5 5 = (4790016000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_5

theorem source_gram_16_5_7 : Z 16 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_7

theorem source_gram_16_5_9 : Z 16 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_9

theorem source_gram_16_5_11 : Z 16 5 11 = (-1496880000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_11

theorem source_gram_16_5_13 : Z 16 5 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_13

theorem source_gram_16_5_15 : Z 16 5 15 = (61297236000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_15

theorem source_gram_16_7_7 : Z 16 7 7 = (1828915200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_7

theorem source_gram_16_7_9 : Z 16 7 9 = (-685843200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_9

theorem source_gram_16_7_11 : Z 16 7 11 = (-1571724000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_11

theorem source_gram_16_7_13 : Z 16 7 13 = (4086482400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_13

theorem source_gram_16_7_15 : Z 16 7 15 = (15324309000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_15

theorem source_gram_16_9_9 : Z 16 9 9 = (457228800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_9

theorem source_gram_16_9_11 : Z 16 9 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_11

theorem source_gram_16_9_13 : Z 16 9 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_13

theorem source_gram_16_9_15 : Z 16 9 15 = (-10216206000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_15

theorem source_gram_16_11_11 : Z 16 11 11 = (3555090000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_11

theorem source_gram_16_11_13 : Z 16 11 13 = (-8027019000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_13

theorem source_gram_16_11_15 : Z 16 11 15 = (-19155386250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_15

theorem source_gram_16_13_13 : Z 16 13 13 = (22183761600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_13_13

theorem source_gram_16_13_15 : Z 16 13 15 = (-19155386250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_13_15

theorem source_gram_16_15_15 : Z 16 15 15 = (2584061605125/2 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_15_15

theorem source_gram_16_3_1 : Z 16 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_3

theorem source_gram_16_5_1 : Z 16 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_5

theorem source_gram_16_5_3 : Z 16 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_5

theorem source_gram_16_7_1 : Z 16 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_7

theorem source_gram_16_7_3 : Z 16 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_7

theorem source_gram_16_7_5 : Z 16 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_7

theorem source_gram_16_9_1 : Z 16 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_9

theorem source_gram_16_9_3 : Z 16 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_9

theorem source_gram_16_9_5 : Z 16 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_9

theorem source_gram_16_9_7 : Z 16 9 7 = (-685843200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_9

theorem source_gram_16_11_1 : Z 16 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_11

theorem source_gram_16_11_3 : Z 16 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_11

theorem source_gram_16_11_5 : Z 16 11 5 = (-1496880000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_11

theorem source_gram_16_11_7 : Z 16 11 7 = (-1571724000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_11

theorem source_gram_16_11_9 : Z 16 11 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_11

theorem source_gram_16_13_1 : Z 16 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_13

theorem source_gram_16_13_3 : Z 16 13 3 = (-7005398400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_13

theorem source_gram_16_13_5 : Z 16 13 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_13

theorem source_gram_16_13_7 : Z 16 13 7 = (4086482400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_13

theorem source_gram_16_13_9 : Z 16 13 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_13

theorem source_gram_16_13_11 : Z 16 13 11 = (-8027019000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_11_13

theorem source_gram_16_15_1 : Z 16 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_15

theorem source_gram_16_15_3 : Z 16 15 3 = (102162060000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_15

theorem source_gram_16_15_5 : Z 16 15 5 = (61297236000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_15

theorem source_gram_16_15_7 : Z 16 15 7 = (15324309000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_15

theorem source_gram_16_15_9 : Z 16 15 9 = (-10216206000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_15

theorem source_gram_16_15_11 : Z 16 15 11 = (-19155386250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_11_15

theorem source_gram_16_15_13 : Z 16 15 13 = (-19155386250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_13_15

theorem gram_16 : gramRational 16 = candidateZ_16 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_16_1_1
  · exact source_gram_16_1_3
  · exact source_gram_16_1_5
  · exact source_gram_16_1_7
  · exact source_gram_16_1_9
  · exact source_gram_16_1_11
  · exact source_gram_16_1_13
  · exact source_gram_16_1_15
  · exact source_gram_16_3_1
  · exact source_gram_16_3_3
  · exact source_gram_16_3_5
  · exact source_gram_16_3_7
  · exact source_gram_16_3_9
  · exact source_gram_16_3_11
  · exact source_gram_16_3_13
  · exact source_gram_16_3_15
  · exact source_gram_16_5_1
  · exact source_gram_16_5_3
  · exact source_gram_16_5_5
  · exact source_gram_16_5_7
  · exact source_gram_16_5_9
  · exact source_gram_16_5_11
  · exact source_gram_16_5_13
  · exact source_gram_16_5_15
  · exact source_gram_16_7_1
  · exact source_gram_16_7_3
  · exact source_gram_16_7_5
  · exact source_gram_16_7_7
  · exact source_gram_16_7_9
  · exact source_gram_16_7_11
  · exact source_gram_16_7_13
  · exact source_gram_16_7_15
  · exact source_gram_16_9_1
  · exact source_gram_16_9_3
  · exact source_gram_16_9_5
  · exact source_gram_16_9_7
  · exact source_gram_16_9_9
  · exact source_gram_16_9_11
  · exact source_gram_16_9_13
  · exact source_gram_16_9_15
  · exact source_gram_16_11_1
  · exact source_gram_16_11_3
  · exact source_gram_16_11_5
  · exact source_gram_16_11_7
  · exact source_gram_16_11_9
  · exact source_gram_16_11_11
  · exact source_gram_16_11_13
  · exact source_gram_16_11_15
  · exact source_gram_16_13_1
  · exact source_gram_16_13_3
  · exact source_gram_16_13_5
  · exact source_gram_16_13_7
  · exact source_gram_16_13_9
  · exact source_gram_16_13_11
  · exact source_gram_16_13_13
  · exact source_gram_16_13_15
  · exact source_gram_16_15_1
  · exact source_gram_16_15_3
  · exact source_gram_16_15_5
  · exact source_gram_16_15_7
  · exact source_gram_16_15_9
  · exact source_gram_16_15_11
  · exact source_gram_16_15_13
  · exact source_gram_16_15_15

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_16 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_16_0_0
  · exact computeLDL_16_0_1
  · exact computeLDL_16_0_2
  · exact computeLDL_16_0_3
  · exact computeLDL_16_0_4
  · exact computeLDL_16_0_5
  · exact computeLDL_16_0_6
  · exact computeLDL_16_0_7
  · exact computeLDL_16_1_0
  · exact computeLDL_16_1_1
  · exact computeLDL_16_1_2
  · exact computeLDL_16_1_3
  · exact computeLDL_16_1_4
  · exact computeLDL_16_1_5
  · exact computeLDL_16_1_6
  · exact computeLDL_16_1_7
  · exact computeLDL_16_2_0
  · exact computeLDL_16_2_1
  · exact computeLDL_16_2_2
  · exact computeLDL_16_2_3
  · exact computeLDL_16_2_4
  · exact computeLDL_16_2_5
  · exact computeLDL_16_2_6
  · exact computeLDL_16_2_7
  · exact computeLDL_16_3_0
  · exact computeLDL_16_3_1
  · exact computeLDL_16_3_2
  · exact computeLDL_16_3_3
  · exact computeLDL_16_3_4
  · exact computeLDL_16_3_5
  · exact computeLDL_16_3_6
  · exact computeLDL_16_3_7
  · exact computeLDL_16_4_0
  · exact computeLDL_16_4_1
  · exact computeLDL_16_4_2
  · exact computeLDL_16_4_3
  · exact computeLDL_16_4_4
  · exact computeLDL_16_4_5
  · exact computeLDL_16_4_6
  · exact computeLDL_16_4_7
  · exact computeLDL_16_5_0
  · exact computeLDL_16_5_1
  · exact computeLDL_16_5_2
  · exact computeLDL_16_5_3
  · exact computeLDL_16_5_4
  · exact computeLDL_16_5_5
  · exact computeLDL_16_5_6
  · exact computeLDL_16_5_7
  · exact computeLDL_16_6_0
  · exact computeLDL_16_6_1
  · exact computeLDL_16_6_2
  · exact computeLDL_16_6_3
  · exact computeLDL_16_6_4
  · exact computeLDL_16_6_5
  · exact computeLDL_16_6_6
  · exact computeLDL_16_6_7
  · exact computeLDL_16_7_0
  · exact computeLDL_16_7_1
  · exact computeLDL_16_7_2
  · exact computeLDL_16_7_3
  · exact computeLDL_16_7_4
  · exact computeLDL_16_7_5
  · exact computeLDL_16_7_6
  · exact computeLDL_16_7_7

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_16 : compressedRational 16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  rw [compressedRational_eq_compute, error_16, gram_16]
  exact candidateLDL_16

theorem four_body_16_positive_oai :
    ((compressedRational 16).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_16 pivots_16 ldl_16
  intro i
  fin_cases i <;> norm_num [pivots_16]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_16_positive_oai := @OAI.Laughlin.Certificate.four_body_16_positive_oai
