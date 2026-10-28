-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_20_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:06.001067+00:00
-- url     : https://prove2.me/submissions/fa47c7a8-2ff3-4e15-9a55-7a61a7cad632

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_20

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_20 : GramCompute.quadruples 20 = [(0,1,2,18), (0,1,3,17), (0,1,4,16), (0,1,5,15), (0,1,6,14), (0,1,7,13), (0,1,8,12), (0,1,9,11), (0,2,3,16), (0,2,4,15), (0,2,5,14), (0,2,6,13), (0,2,7,12), (0,2,8,11), (0,2,9,10), (0,3,4,14), (0,3,5,13), (0,3,6,12), (0,3,7,11), (0,3,8,10), (0,4,5,12), (0,4,6,11), (0,4,7,10), (0,4,8,9), (0,5,6,10), (0,5,7,9), (0,6,7,8), (1,2,3,15), (1,2,4,14), (1,2,5,13), (1,2,6,12), (1,2,7,11), (1,2,8,10), (1,3,4,13), (1,3,5,12), (1,3,6,11), (1,3,7,10), (1,3,8,9), (1,4,5,11), (1,4,6,10), (1,4,7,9), (1,5,6,9), (1,5,7,8), (2,3,4,12), (2,3,5,11), (2,3,6,10), (2,3,7,9), (2,4,5,10), (2,4,6,9), (2,4,7,8), (2,5,6,8), (3,4,5,9), (3,4,6,8), (3,5,6,7)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_1_1 : GramCompute.ZFast 20 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_3 : GramCompute.ZFast 20 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_5 : GramCompute.ZFast 20 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_7 : GramCompute.ZFast 20 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_9 : GramCompute.ZFast 20 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_11 : GramCompute.ZFast 20 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_13 : GramCompute.ZFast 20 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_15 : GramCompute.ZFast 20 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_17 : GramCompute.ZFast 20 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_19 : GramCompute.ZFast 20 1 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_3_3 : GramCompute.ZFast 20 3 3 = (2134124568576000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_5 : GramCompute.ZFast 20 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_7 : GramCompute.ZFast 20 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_9 : GramCompute.ZFast 20 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_11 : GramCompute.ZFast 20 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_13 : GramCompute.ZFast 20 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_15 : GramCompute.ZFast 20 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_17 : GramCompute.ZFast 20 3 17 = (-133382785536000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_19 : GramCompute.ZFast 20 3 19 = (3326233214304000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_5_5 : GramCompute.ZFast 20 5 5 = (156920924160000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_7 : GramCompute.ZFast 20 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_9 : GramCompute.ZFast 20 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_11 : GramCompute.ZFast 20 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_13 : GramCompute.ZFast 20 5 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_15 : GramCompute.ZFast 20 5 15 = (-17163226080000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_17 : GramCompute.ZFast 20 5 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_5_19 : GramCompute.ZFast 20 5 19 = (2375880867360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_7_7 : GramCompute.ZFast 20 7 7 = (31384184832000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_9 : GramCompute.ZFast 20 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_11 : GramCompute.ZFast 20 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_13 : GramCompute.ZFast 20 7 13 = (-4413400992000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_15 : GramCompute.ZFast 20 7 15 = (-21454032600000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_17 : GramCompute.ZFast 20 7 17 = (116709937344000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_7_19 : GramCompute.ZFast 20 7 19 = (1069146390312000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_9_9 : GramCompute.ZFast 20 9 9 = (14485008384000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_9_11 : GramCompute.ZFast 20 9 11 = (-2263282560000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_9_13 : GramCompute.ZFast 20 9 13 = (-11769069312000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_9_15 : GramCompute.ZFast 20 9 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_9_17 : GramCompute.ZFast 20 9 17 = (100037089152000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_9_19 : GramCompute.ZFast 20 9 19 = (237588086736000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_11_11 : GramCompute.ZFast 20 11 11 = (5148967824000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_11_13 : GramCompute.ZFast 20 11 13 = (-8091235152000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_11_15 : GramCompute.ZFast 20 11 15 = (10114043940000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_11_17 : GramCompute.ZFast 20 11 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_11_19 : GramCompute.ZFast 20 11 19 = (-148492554210000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_13_13 : GramCompute.ZFast 20 13 13 = (31384184832000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_15 : GramCompute.ZFast 20 13 15 = (-21913761870000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_17 : GramCompute.ZFast 20 13 17 = (-108373513248000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_19 : GramCompute.ZFast 20 13 19 = (-267286597578000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram15Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_15_15 : GramCompute.ZFast 20 15 15 = (62791356127500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_15_17 : GramCompute.ZFast 20 15 17 = (-182359277100000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_15_19 : GramCompute.ZFast 20 15 19 = (-259861969867500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram17Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_17_17 : GramCompute.ZFast 20 17 17 = (1921545754128000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_17_19 : GramCompute.ZFast 20 17 19 = (-207889575894000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram191920
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_19_19 : GramCompute.ZFast 20 19 19 = (121494751697694375 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_0_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_0_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 0 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_1_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_1_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 1 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 1 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_2_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_2_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 2 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 2 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_3_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_3_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 3 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 3 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_4_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_4_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 4 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 4 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_5_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_5_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 5 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 5 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_6_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_6_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 6 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 6 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_7_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_7_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 7 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 7 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL08Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_8_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_8_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 8 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 8 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL09Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_20_9_0 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 0 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_1 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 1 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_2 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 2 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_3 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 3 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_4 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 4 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_5 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 5 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_6 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 6 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_7 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 7 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_8 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 8 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_20_9_9 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 9 9 =
    (lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose) 9 9 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_20_1_1 : Z 20 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_1

theorem source_gram_20_1_3 : Z 20 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_3

theorem source_gram_20_1_5 : Z 20 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_5

theorem source_gram_20_1_7 : Z 20 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_7

theorem source_gram_20_1_9 : Z 20 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_9

theorem source_gram_20_1_11 : Z 20 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_11

theorem source_gram_20_1_13 : Z 20 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_13

theorem source_gram_20_1_15 : Z 20 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_15

theorem source_gram_20_1_17 : Z 20 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_17

theorem source_gram_20_1_19 : Z 20 1 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_19

theorem source_gram_20_3_3 : Z 20 3 3 = (2134124568576000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_3

theorem source_gram_20_3_5 : Z 20 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_5

theorem source_gram_20_3_7 : Z 20 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_7

theorem source_gram_20_3_9 : Z 20 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_9

theorem source_gram_20_3_11 : Z 20 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_11

theorem source_gram_20_3_13 : Z 20 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_13

theorem source_gram_20_3_15 : Z 20 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_15

theorem source_gram_20_3_17 : Z 20 3 17 = (-133382785536000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_17

theorem source_gram_20_3_19 : Z 20 3 19 = (3326233214304000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_19

theorem source_gram_20_5_5 : Z 20 5 5 = (156920924160000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_5

theorem source_gram_20_5_7 : Z 20 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_7

theorem source_gram_20_5_9 : Z 20 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_9

theorem source_gram_20_5_11 : Z 20 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_11

theorem source_gram_20_5_13 : Z 20 5 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_13

theorem source_gram_20_5_15 : Z 20 5 15 = (-17163226080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_15

theorem source_gram_20_5_17 : Z 20 5 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_17

theorem source_gram_20_5_19 : Z 20 5 19 = (2375880867360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_5_19

theorem source_gram_20_7_7 : Z 20 7 7 = (31384184832000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_7

theorem source_gram_20_7_9 : Z 20 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_9

theorem source_gram_20_7_11 : Z 20 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_11

theorem source_gram_20_7_13 : Z 20 7 13 = (-4413400992000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_13

theorem source_gram_20_7_15 : Z 20 7 15 = (-21454032600000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_15

theorem source_gram_20_7_17 : Z 20 7 17 = (116709937344000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_17

theorem source_gram_20_7_19 : Z 20 7 19 = (1069146390312000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_7_19

theorem source_gram_20_9_9 : Z 20 9 9 = (14485008384000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_9

theorem source_gram_20_9_11 : Z 20 9 11 = (-2263282560000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_11

theorem source_gram_20_9_13 : Z 20 9 13 = (-11769069312000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_13

theorem source_gram_20_9_15 : Z 20 9 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_15

theorem source_gram_20_9_17 : Z 20 9 17 = (100037089152000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_17

theorem source_gram_20_9_19 : Z 20 9 19 = (237588086736000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_9_19

theorem source_gram_20_11_11 : Z 20 11 11 = (5148967824000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_11_11

theorem source_gram_20_11_13 : Z 20 11 13 = (-8091235152000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_11_13

theorem source_gram_20_11_15 : Z 20 11 15 = (10114043940000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_11_15

theorem source_gram_20_11_17 : Z 20 11 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_11_17

theorem source_gram_20_11_19 : Z 20 11 19 = (-148492554210000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_11_19

theorem source_gram_20_13_13 : Z 20 13 13 = (31384184832000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_13_13

theorem source_gram_20_13_15 : Z 20 13 15 = (-21913761870000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_13_15

theorem source_gram_20_13_17 : Z 20 13 17 = (-108373513248000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_13_17

theorem source_gram_20_13_19 : Z 20 13 19 = (-267286597578000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_13_19

theorem source_gram_20_15_15 : Z 20 15 15 = (62791356127500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_15_15

theorem source_gram_20_15_17 : Z 20 15 17 = (-182359277100000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_15_17

theorem source_gram_20_15_19 : Z 20 15 19 = (-259861969867500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_15_19

theorem source_gram_20_17_17 : Z 20 17 17 = (1921545754128000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_17_17

theorem source_gram_20_17_19 : Z 20 17 19 = (-207889575894000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_17_19

theorem source_gram_20_19_19 : Z 20 19 19 = (121494751697694375 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_19_19

theorem source_gram_20_3_1 : Z 20 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_3

theorem source_gram_20_5_1 : Z 20 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_5

theorem source_gram_20_5_3 : Z 20 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_5

theorem source_gram_20_7_1 : Z 20 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_7

theorem source_gram_20_7_3 : Z 20 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_7

theorem source_gram_20_7_5 : Z 20 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_7

theorem source_gram_20_9_1 : Z 20 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_9

theorem source_gram_20_9_3 : Z 20 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_9

theorem source_gram_20_9_5 : Z 20 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_9

theorem source_gram_20_9_7 : Z 20 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_9

theorem source_gram_20_11_1 : Z 20 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_11

theorem source_gram_20_11_3 : Z 20 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_11

theorem source_gram_20_11_5 : Z 20 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_11

theorem source_gram_20_11_7 : Z 20 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_11

theorem source_gram_20_11_9 : Z 20 11 9 = (-2263282560000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_9_11

theorem source_gram_20_13_1 : Z 20 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_13

theorem source_gram_20_13_3 : Z 20 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_13

theorem source_gram_20_13_5 : Z 20 13 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_13

theorem source_gram_20_13_7 : Z 20 13 7 = (-4413400992000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_13

theorem source_gram_20_13_9 : Z 20 13 9 = (-11769069312000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_9_13

theorem source_gram_20_13_11 : Z 20 13 11 = (-8091235152000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_11_13

theorem source_gram_20_15_1 : Z 20 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_15

theorem source_gram_20_15_3 : Z 20 15 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_15

theorem source_gram_20_15_5 : Z 20 15 5 = (-17163226080000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_15

theorem source_gram_20_15_7 : Z 20 15 7 = (-21454032600000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_15

theorem source_gram_20_15_9 : Z 20 15 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_9_15

theorem source_gram_20_15_11 : Z 20 15 11 = (10114043940000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_11_15

theorem source_gram_20_15_13 : Z 20 15 13 = (-21913761870000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_13_15

theorem source_gram_20_17_1 : Z 20 17 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_17

theorem source_gram_20_17_3 : Z 20 17 3 = (-133382785536000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_17

theorem source_gram_20_17_5 : Z 20 17 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_17

theorem source_gram_20_17_7 : Z 20 17 7 = (116709937344000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_17

theorem source_gram_20_17_9 : Z 20 17 9 = (100037089152000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_9_17

theorem source_gram_20_17_11 : Z 20 17 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_11_17

theorem source_gram_20_17_13 : Z 20 17 13 = (-108373513248000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_13_17

theorem source_gram_20_17_15 : Z 20 17 15 = (-182359277100000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_15_17

theorem source_gram_20_19_1 : Z 20 19 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_1_19

theorem source_gram_20_19_3 : Z 20 19 3 = (3326233214304000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_3_19

theorem source_gram_20_19_5 : Z 20 19 5 = (2375880867360000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_5_19

theorem source_gram_20_19_7 : Z 20 19 7 = (1069146390312000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_7_19

theorem source_gram_20_19_9 : Z 20 19 9 = (237588086736000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_9_19

theorem source_gram_20_19_11 : Z 20 19 11 = (-148492554210000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_11_19

theorem source_gram_20_19_13 : Z 20 19 13 = (-267286597578000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_13_19

theorem source_gram_20_19_15 : Z 20 19 15 = (-259861969867500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_15_19

theorem source_gram_20_19_17 : Z 20 19 17 = (-207889575894000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_20_17_19

theorem gram_20 : gramRational 20 = candidateZ_20 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_20_1_1
  · exact source_gram_20_1_3
  · exact source_gram_20_1_5
  · exact source_gram_20_1_7
  · exact source_gram_20_1_9
  · exact source_gram_20_1_11
  · exact source_gram_20_1_13
  · exact source_gram_20_1_15
  · exact source_gram_20_1_17
  · exact source_gram_20_1_19
  · exact source_gram_20_3_1
  · exact source_gram_20_3_3
  · exact source_gram_20_3_5
  · exact source_gram_20_3_7
  · exact source_gram_20_3_9
  · exact source_gram_20_3_11
  · exact source_gram_20_3_13
  · exact source_gram_20_3_15
  · exact source_gram_20_3_17
  · exact source_gram_20_3_19
  · exact source_gram_20_5_1
  · exact source_gram_20_5_3
  · exact source_gram_20_5_5
  · exact source_gram_20_5_7
  · exact source_gram_20_5_9
  · exact source_gram_20_5_11
  · exact source_gram_20_5_13
  · exact source_gram_20_5_15
  · exact source_gram_20_5_17
  · exact source_gram_20_5_19
  · exact source_gram_20_7_1
  · exact source_gram_20_7_3
  · exact source_gram_20_7_5
  · exact source_gram_20_7_7
  · exact source_gram_20_7_9
  · exact source_gram_20_7_11
  · exact source_gram_20_7_13
  · exact source_gram_20_7_15
  · exact source_gram_20_7_17
  · exact source_gram_20_7_19
  · exact source_gram_20_9_1
  · exact source_gram_20_9_3
  · exact source_gram_20_9_5
  · exact source_gram_20_9_7
  · exact source_gram_20_9_9
  · exact source_gram_20_9_11
  · exact source_gram_20_9_13
  · exact source_gram_20_9_15
  · exact source_gram_20_9_17
  · exact source_gram_20_9_19
  · exact source_gram_20_11_1
  · exact source_gram_20_11_3
  · exact source_gram_20_11_5
  · exact source_gram_20_11_7
  · exact source_gram_20_11_9
  · exact source_gram_20_11_11
  · exact source_gram_20_11_13
  · exact source_gram_20_11_15
  · exact source_gram_20_11_17
  · exact source_gram_20_11_19
  · exact source_gram_20_13_1
  · exact source_gram_20_13_3
  · exact source_gram_20_13_5
  · exact source_gram_20_13_7
  · exact source_gram_20_13_9
  · exact source_gram_20_13_11
  · exact source_gram_20_13_13
  · exact source_gram_20_13_15
  · exact source_gram_20_13_17
  · exact source_gram_20_13_19
  · exact source_gram_20_15_1
  · exact source_gram_20_15_3
  · exact source_gram_20_15_5
  · exact source_gram_20_15_7
  · exact source_gram_20_15_9
  · exact source_gram_20_15_11
  · exact source_gram_20_15_13
  · exact source_gram_20_15_15
  · exact source_gram_20_15_17
  · exact source_gram_20_15_19
  · exact source_gram_20_17_1
  · exact source_gram_20_17_3
  · exact source_gram_20_17_5
  · exact source_gram_20_17_7
  · exact source_gram_20_17_9
  · exact source_gram_20_17_11
  · exact source_gram_20_17_13
  · exact source_gram_20_17_15
  · exact source_gram_20_17_17
  · exact source_gram_20_17_19
  · exact source_gram_20_19_1
  · exact source_gram_20_19_3
  · exact source_gram_20_19_5
  · exact source_gram_20_19_7
  · exact source_gram_20_19_9
  · exact source_gram_20_19_11
  · exact source_gram_20_19_13
  · exact source_gram_20_19_15
  · exact source_gram_20_19_17
  · exact source_gram_20_19_19

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_20 : MatrixCompute.compressed 20 candidateY_20 candidateZ_20 =
    lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_20_0_0
  · exact computeLDL_20_0_1
  · exact computeLDL_20_0_2
  · exact computeLDL_20_0_3
  · exact computeLDL_20_0_4
  · exact computeLDL_20_0_5
  · exact computeLDL_20_0_6
  · exact computeLDL_20_0_7
  · exact computeLDL_20_0_8
  · exact computeLDL_20_0_9
  · exact computeLDL_20_1_0
  · exact computeLDL_20_1_1
  · exact computeLDL_20_1_2
  · exact computeLDL_20_1_3
  · exact computeLDL_20_1_4
  · exact computeLDL_20_1_5
  · exact computeLDL_20_1_6
  · exact computeLDL_20_1_7
  · exact computeLDL_20_1_8
  · exact computeLDL_20_1_9
  · exact computeLDL_20_2_0
  · exact computeLDL_20_2_1
  · exact computeLDL_20_2_2
  · exact computeLDL_20_2_3
  · exact computeLDL_20_2_4
  · exact computeLDL_20_2_5
  · exact computeLDL_20_2_6
  · exact computeLDL_20_2_7
  · exact computeLDL_20_2_8
  · exact computeLDL_20_2_9
  · exact computeLDL_20_3_0
  · exact computeLDL_20_3_1
  · exact computeLDL_20_3_2
  · exact computeLDL_20_3_3
  · exact computeLDL_20_3_4
  · exact computeLDL_20_3_5
  · exact computeLDL_20_3_6
  · exact computeLDL_20_3_7
  · exact computeLDL_20_3_8
  · exact computeLDL_20_3_9
  · exact computeLDL_20_4_0
  · exact computeLDL_20_4_1
  · exact computeLDL_20_4_2
  · exact computeLDL_20_4_3
  · exact computeLDL_20_4_4
  · exact computeLDL_20_4_5
  · exact computeLDL_20_4_6
  · exact computeLDL_20_4_7
  · exact computeLDL_20_4_8
  · exact computeLDL_20_4_9
  · exact computeLDL_20_5_0
  · exact computeLDL_20_5_1
  · exact computeLDL_20_5_2
  · exact computeLDL_20_5_3
  · exact computeLDL_20_5_4
  · exact computeLDL_20_5_5
  · exact computeLDL_20_5_6
  · exact computeLDL_20_5_7
  · exact computeLDL_20_5_8
  · exact computeLDL_20_5_9
  · exact computeLDL_20_6_0
  · exact computeLDL_20_6_1
  · exact computeLDL_20_6_2
  · exact computeLDL_20_6_3
  · exact computeLDL_20_6_4
  · exact computeLDL_20_6_5
  · exact computeLDL_20_6_6
  · exact computeLDL_20_6_7
  · exact computeLDL_20_6_8
  · exact computeLDL_20_6_9
  · exact computeLDL_20_7_0
  · exact computeLDL_20_7_1
  · exact computeLDL_20_7_2
  · exact computeLDL_20_7_3
  · exact computeLDL_20_7_4
  · exact computeLDL_20_7_5
  · exact computeLDL_20_7_6
  · exact computeLDL_20_7_7
  · exact computeLDL_20_7_8
  · exact computeLDL_20_7_9
  · exact computeLDL_20_8_0
  · exact computeLDL_20_8_1
  · exact computeLDL_20_8_2
  · exact computeLDL_20_8_3
  · exact computeLDL_20_8_4
  · exact computeLDL_20_8_5
  · exact computeLDL_20_8_6
  · exact computeLDL_20_8_7
  · exact computeLDL_20_8_8
  · exact computeLDL_20_8_9
  · exact computeLDL_20_9_0
  · exact computeLDL_20_9_1
  · exact computeLDL_20_9_2
  · exact computeLDL_20_9_3
  · exact computeLDL_20_9_4
  · exact computeLDL_20_9_5
  · exact computeLDL_20_9_6
  · exact computeLDL_20_9_7
  · exact computeLDL_20_9_8
  · exact computeLDL_20_9_9

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_20 : compressedRational 20 =
    lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose := by
  rw [compressedRational_eq_compute, error_20, gram_20]
  exact candidateLDL_20

theorem four_body_20_positive_oai :
    ((compressedRational 20).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_20 pivots_20 ldl_20
  intro i
  fin_cases i <;> norm_num [pivots_20]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_20_positive_oai := @OAI.Laughlin.Certificate.four_body_20_positive_oai
