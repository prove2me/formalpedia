-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_13_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:13:22.048153+00:00
-- url     : https://prove2.me/submissions/b4c380f0-d6ec-4d57-b285-9cd804142fe5

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_13

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_13 : GramCompute.quadruples 13 = [(0,1,2,11), (0,1,3,10), (0,1,4,9), (0,1,5,8), (0,1,6,7), (0,2,3,9), (0,2,4,8), (0,2,5,7), (0,3,4,7), (0,3,5,6), (1,2,3,8), (1,2,4,7), (1,2,5,6), (1,3,4,6), (2,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_1_1 : GramCompute.ZFast 13 1 1 = (958003200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_3 : GramCompute.ZFast 13 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_5 : GramCompute.ZFast 13 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_7 : GramCompute.ZFast 13 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_9 : GramCompute.ZFast 13 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_11 : GramCompute.ZFast 13 1 11 = (-29937600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_13 : GramCompute.ZFast 13 1 13 = (972972000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_3_3 : GramCompute.ZFast 13 3 3 = (21772800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_5 : GramCompute.ZFast 13 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_7 : GramCompute.ZFast 13 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_9 : GramCompute.ZFast 13 3 9 = (-2721600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_11 : GramCompute.ZFast 13 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_13 : GramCompute.ZFast 13 3 13 = (291891600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_5_5 : GramCompute.ZFast 13 5 5 = (4838400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_7 : GramCompute.ZFast 13 5 7 = (-907200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_9 : GramCompute.ZFast 13 5 9 = (-4082400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_11 : GramCompute.ZFast 13 5 11 = (12474000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_13 : GramCompute.ZFast 13 5 13 = (48648600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_7_7 : GramCompute.ZFast 13 7 7 = (453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_9 : GramCompute.ZFast 13 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_11 : GramCompute.ZFast 13 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_13 : GramCompute.ZFast 13 7 13 = (-24324300 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_9_9 : GramCompute.ZFast 13 9 9 = (5851440 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_9_11 : GramCompute.ZFast 13 9 11 = (-16839900 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_9_13 : GramCompute.ZFast 13 9 13 = (-36486450 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_11_11 : GramCompute.ZFast 13 11 11 = (52390800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_11_13 : GramCompute.ZFast 13 11 13 = (-30405375 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram131313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_13_13 : GramCompute.ZFast 13 13 13 = (12411474075/2 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_0_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_0_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 0 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_1_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_1_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 1 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_2_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_2_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 2 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_3_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_3_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 3 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_4_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_4_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 4 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_5_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_5_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 5 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_13_6_0 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 0 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_1 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 1 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_2 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 2 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_3 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 3 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_4 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 4 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_5 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 5 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_13_6_6 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 6 6 =
    (lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose) 6 6 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_13_1_1 : Z 13 1 1 = (958003200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_1

theorem source_gram_13_1_3 : Z 13 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_3

theorem source_gram_13_1_5 : Z 13 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_5

theorem source_gram_13_1_7 : Z 13 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_7

theorem source_gram_13_1_9 : Z 13 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_9

theorem source_gram_13_1_11 : Z 13 1 11 = (-29937600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_11

theorem source_gram_13_1_13 : Z 13 1 13 = (972972000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_13

theorem source_gram_13_3_3 : Z 13 3 3 = (21772800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_3

theorem source_gram_13_3_5 : Z 13 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_5

theorem source_gram_13_3_7 : Z 13 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_7

theorem source_gram_13_3_9 : Z 13 3 9 = (-2721600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_9

theorem source_gram_13_3_11 : Z 13 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_11

theorem source_gram_13_3_13 : Z 13 3 13 = (291891600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_13

theorem source_gram_13_5_5 : Z 13 5 5 = (4838400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_5

theorem source_gram_13_5_7 : Z 13 5 7 = (-907200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_7

theorem source_gram_13_5_9 : Z 13 5 9 = (-4082400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_9

theorem source_gram_13_5_11 : Z 13 5 11 = (12474000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_11

theorem source_gram_13_5_13 : Z 13 5 13 = (48648600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_13

theorem source_gram_13_7_7 : Z 13 7 7 = (453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_7

theorem source_gram_13_7_9 : Z 13 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_9

theorem source_gram_13_7_11 : Z 13 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_11

theorem source_gram_13_7_13 : Z 13 7 13 = (-24324300 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_13

theorem source_gram_13_9_9 : Z 13 9 9 = (5851440 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_9

theorem source_gram_13_9_11 : Z 13 9 11 = (-16839900 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_11

theorem source_gram_13_9_13 : Z 13 9 13 = (-36486450 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_13

theorem source_gram_13_11_11 : Z 13 11 11 = (52390800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_11_11

theorem source_gram_13_11_13 : Z 13 11 13 = (-30405375 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_11_13

theorem source_gram_13_13_13 : Z 13 13 13 = (12411474075/2 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_13_13

theorem source_gram_13_3_1 : Z 13 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_3

theorem source_gram_13_5_1 : Z 13 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_5

theorem source_gram_13_5_3 : Z 13 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_5

theorem source_gram_13_7_1 : Z 13 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_7

theorem source_gram_13_7_3 : Z 13 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_7

theorem source_gram_13_7_5 : Z 13 7 5 = (-907200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_7

theorem source_gram_13_9_1 : Z 13 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_9

theorem source_gram_13_9_3 : Z 13 9 3 = (-2721600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_9

theorem source_gram_13_9_5 : Z 13 9 5 = (-4082400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_9

theorem source_gram_13_9_7 : Z 13 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_9

theorem source_gram_13_11_1 : Z 13 11 1 = (-29937600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_11

theorem source_gram_13_11_3 : Z 13 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_11

theorem source_gram_13_11_5 : Z 13 11 5 = (12474000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_11

theorem source_gram_13_11_7 : Z 13 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_11

theorem source_gram_13_11_9 : Z 13 11 9 = (-16839900 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_9_11

theorem source_gram_13_13_1 : Z 13 13 1 = (972972000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_13

theorem source_gram_13_13_3 : Z 13 13 3 = (291891600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_13

theorem source_gram_13_13_5 : Z 13 13 5 = (48648600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_13

theorem source_gram_13_13_7 : Z 13 13 7 = (-24324300 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_13

theorem source_gram_13_13_9 : Z 13 13 9 = (-36486450 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_9_13

theorem source_gram_13_13_11 : Z 13 13 11 = (-30405375 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_11_13

theorem gram_13 : gramRational 13 = candidateZ_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_13_1_1
  · exact source_gram_13_1_3
  · exact source_gram_13_1_5
  · exact source_gram_13_1_7
  · exact source_gram_13_1_9
  · exact source_gram_13_1_11
  · exact source_gram_13_1_13
  · exact source_gram_13_3_1
  · exact source_gram_13_3_3
  · exact source_gram_13_3_5
  · exact source_gram_13_3_7
  · exact source_gram_13_3_9
  · exact source_gram_13_3_11
  · exact source_gram_13_3_13
  · exact source_gram_13_5_1
  · exact source_gram_13_5_3
  · exact source_gram_13_5_5
  · exact source_gram_13_5_7
  · exact source_gram_13_5_9
  · exact source_gram_13_5_11
  · exact source_gram_13_5_13
  · exact source_gram_13_7_1
  · exact source_gram_13_7_3
  · exact source_gram_13_7_5
  · exact source_gram_13_7_7
  · exact source_gram_13_7_9
  · exact source_gram_13_7_11
  · exact source_gram_13_7_13
  · exact source_gram_13_9_1
  · exact source_gram_13_9_3
  · exact source_gram_13_9_5
  · exact source_gram_13_9_7
  · exact source_gram_13_9_9
  · exact source_gram_13_9_11
  · exact source_gram_13_9_13
  · exact source_gram_13_11_1
  · exact source_gram_13_11_3
  · exact source_gram_13_11_5
  · exact source_gram_13_11_7
  · exact source_gram_13_11_9
  · exact source_gram_13_11_11
  · exact source_gram_13_11_13
  · exact source_gram_13_13_1
  · exact source_gram_13_13_3
  · exact source_gram_13_13_5
  · exact source_gram_13_13_7
  · exact source_gram_13_13_9
  · exact source_gram_13_13_11
  · exact source_gram_13_13_13

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_13 : MatrixCompute.compressed 13 candidateY_13 candidateZ_13 =
    lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_13_0_0
  · exact computeLDL_13_0_1
  · exact computeLDL_13_0_2
  · exact computeLDL_13_0_3
  · exact computeLDL_13_0_4
  · exact computeLDL_13_0_5
  · exact computeLDL_13_0_6
  · exact computeLDL_13_1_0
  · exact computeLDL_13_1_1
  · exact computeLDL_13_1_2
  · exact computeLDL_13_1_3
  · exact computeLDL_13_1_4
  · exact computeLDL_13_1_5
  · exact computeLDL_13_1_6
  · exact computeLDL_13_2_0
  · exact computeLDL_13_2_1
  · exact computeLDL_13_2_2
  · exact computeLDL_13_2_3
  · exact computeLDL_13_2_4
  · exact computeLDL_13_2_5
  · exact computeLDL_13_2_6
  · exact computeLDL_13_3_0
  · exact computeLDL_13_3_1
  · exact computeLDL_13_3_2
  · exact computeLDL_13_3_3
  · exact computeLDL_13_3_4
  · exact computeLDL_13_3_5
  · exact computeLDL_13_3_6
  · exact computeLDL_13_4_0
  · exact computeLDL_13_4_1
  · exact computeLDL_13_4_2
  · exact computeLDL_13_4_3
  · exact computeLDL_13_4_4
  · exact computeLDL_13_4_5
  · exact computeLDL_13_4_6
  · exact computeLDL_13_5_0
  · exact computeLDL_13_5_1
  · exact computeLDL_13_5_2
  · exact computeLDL_13_5_3
  · exact computeLDL_13_5_4
  · exact computeLDL_13_5_5
  · exact computeLDL_13_5_6
  · exact computeLDL_13_6_0
  · exact computeLDL_13_6_1
  · exact computeLDL_13_6_2
  · exact computeLDL_13_6_3
  · exact computeLDL_13_6_4
  · exact computeLDL_13_6_5
  · exact computeLDL_13_6_6

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_13 : compressedRational 13 =
    lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  rw [compressedRational_eq_compute, error_13, gram_13]
  exact candidateLDL_13

theorem four_body_13_positive_oai :
    ((compressedRational 13).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_13 pivots_13 ldl_13
  intro i
  fin_cases i <;> norm_num [pivots_13]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_13_positive_oai := @OAI.Laughlin.Certificate.four_body_13_positive_oai
