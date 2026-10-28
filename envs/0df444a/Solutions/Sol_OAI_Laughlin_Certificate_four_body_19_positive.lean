-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_19_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:38.897206+00:00
-- url     : https://prove2.me/submissions/2d185c0f-4d87-4add-92a7-14786b90339d

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_19

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_19 : GramCompute.quadruples 19 = [(0,1,2,17), (0,1,3,16), (0,1,4,15), (0,1,5,14), (0,1,6,13), (0,1,7,12), (0,1,8,11), (0,1,9,10), (0,2,3,15), (0,2,4,14), (0,2,5,13), (0,2,6,12), (0,2,7,11), (0,2,8,10), (0,3,4,13), (0,3,5,12), (0,3,6,11), (0,3,7,10), (0,3,8,9), (0,4,5,11), (0,4,6,10), (0,4,7,9), (0,5,6,9), (0,5,7,8), (1,2,3,14), (1,2,4,13), (1,2,5,12), (1,2,6,11), (1,2,7,10), (1,2,8,9), (1,3,4,12), (1,3,5,11), (1,3,6,10), (1,3,7,9), (1,4,5,10), (1,4,6,9), (1,4,7,8), (1,5,6,8), (2,3,4,11), (2,3,5,10), (2,3,6,9), (2,3,7,8), (2,4,5,9), (2,4,6,8), (2,5,6,7), (3,4,5,8), (3,4,6,7)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_1_1 : GramCompute.ZFast 19 1 1 = (12804747411456000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_3 : GramCompute.ZFast 19 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_5 : GramCompute.ZFast 19 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_7 : GramCompute.ZFast 19 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_9 : GramCompute.ZFast 19 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_11 : GramCompute.ZFast 19 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_13 : GramCompute.ZFast 19 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_15 : GramCompute.ZFast 19 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_17 : GramCompute.ZFast 19 1 17 = (-50018544576000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_1_19 : GramCompute.ZFast 19 1 19 = (3801409387776000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_3_3 : GramCompute.ZFast 19 3 3 = (125536739328000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_5 : GramCompute.ZFast 19 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_7 : GramCompute.ZFast 19 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_9 : GramCompute.ZFast 19 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_11 : GramCompute.ZFast 19 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_13 : GramCompute.ZFast 19 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_15 : GramCompute.ZFast 19 3 15 = (-1961511552000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_17 : GramCompute.ZFast 19 3 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_3_19 : GramCompute.ZFast 19 3 19 = (1425528520416000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_5_5 : GramCompute.ZFast 19 5 5 = (10461394944000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_7 : GramCompute.ZFast 19 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_9 : GramCompute.ZFast 19 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_11 : GramCompute.ZFast 19 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_13 : GramCompute.ZFast 19 5 13 = (-245188944000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_15 : GramCompute.ZFast 19 5 15 = (-3677834160000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_17 : GramCompute.ZFast 19 5 17 = (34735100400000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_5_19 : GramCompute.ZFast 19 5 19 = (475176173472000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_7_7 : GramCompute.ZFast 19 7 7 = (2414168064000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_9 : GramCompute.ZFast 19 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_11 : GramCompute.ZFast 19 7 11 = (-75442752000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_13 : GramCompute.ZFast 19 7 13 = (-1225944720000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_15 : GramCompute.ZFast 19 7 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_17 : GramCompute.ZFast 19 7 17 = (29177484336000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_7_19 : GramCompute.ZFast 19 7 19 = (118794043368000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_9_9 : GramCompute.ZFast 19 9 9 = (1265380704000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_9_11 : GramCompute.ZFast 19 9 11 = (-678984768000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_9_13 : GramCompute.ZFast 19 9 13 = (-1103350248000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_9_15 : GramCompute.ZFast 19 9 15 = (2574483912000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_9_17 : GramCompute.ZFast 19 9 17 = (9378477108000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_9_19 : GramCompute.ZFast 19 9 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_11_11 : GramCompute.ZFast 19 11 11 = (572107536000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_13 : GramCompute.ZFast 19 11 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_15 : GramCompute.ZFast 19 11 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_17 : GramCompute.ZFast 19 11 17 = (-7641722088000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_19 : GramCompute.ZFast 19 11 19 = (-29698510842000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_13_13 : GramCompute.ZFast 19 13 13 = (3544293753000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_15 : GramCompute.ZFast 19 13 15 = (-6574128561000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_17 : GramCompute.ZFast 19 13 17 = (-16933361445000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_19 : GramCompute.ZFast 19 13 19 = (-29698510842000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram15Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_15_15 : GramCompute.ZFast 19 15 15 = (17439063642000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_15_17 : GramCompute.ZFast 19 15 17 = (-19538493975000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_15_19 : GramCompute.ZFast 19 15 19 = (-22273883131500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram17Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_17_17 : GramCompute.ZFast 19 17 17 = (693290894546250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_17_19 : GramCompute.ZFast 19 17 19 = (-14849255421000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram191919
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_19_19 : GramCompute.ZFast 19 19 19 = (121635819624193875 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_0_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_1_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_2_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_2_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 2 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 2 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_3_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_3_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 3 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 3 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_4_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_4_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 4 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 4 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_5_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_5_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 5 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 5 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_6_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_6_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 6 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 6 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_7_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_7_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 7 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 7 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL08Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_8_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_8_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 8 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 8 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL09Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_9_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_9_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 9 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 9 9 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_19_1_1 : Z 19 1 1 = (12804747411456000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_1

theorem source_gram_19_1_3 : Z 19 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_3

theorem source_gram_19_1_5 : Z 19 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_5

theorem source_gram_19_1_7 : Z 19 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_7

theorem source_gram_19_1_9 : Z 19 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_9

theorem source_gram_19_1_11 : Z 19 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_11

theorem source_gram_19_1_13 : Z 19 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_13

theorem source_gram_19_1_15 : Z 19 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_15

theorem source_gram_19_1_17 : Z 19 1 17 = (-50018544576000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_17

theorem source_gram_19_1_19 : Z 19 1 19 = (3801409387776000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_1_19

theorem source_gram_19_3_3 : Z 19 3 3 = (125536739328000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_3

theorem source_gram_19_3_5 : Z 19 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_5

theorem source_gram_19_3_7 : Z 19 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_7

theorem source_gram_19_3_9 : Z 19 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_9

theorem source_gram_19_3_11 : Z 19 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_11

theorem source_gram_19_3_13 : Z 19 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_13

theorem source_gram_19_3_15 : Z 19 3 15 = (-1961511552000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_15

theorem source_gram_19_3_17 : Z 19 3 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_17

theorem source_gram_19_3_19 : Z 19 3 19 = (1425528520416000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_3_19

theorem source_gram_19_5_5 : Z 19 5 5 = (10461394944000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_5

theorem source_gram_19_5_7 : Z 19 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_7

theorem source_gram_19_5_9 : Z 19 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_9

theorem source_gram_19_5_11 : Z 19 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_11

theorem source_gram_19_5_13 : Z 19 5 13 = (-245188944000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_13

theorem source_gram_19_5_15 : Z 19 5 15 = (-3677834160000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_15

theorem source_gram_19_5_17 : Z 19 5 17 = (34735100400000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_17

theorem source_gram_19_5_19 : Z 19 5 19 = (475176173472000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_5_19

theorem source_gram_19_7_7 : Z 19 7 7 = (2414168064000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_7

theorem source_gram_19_7_9 : Z 19 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_9

theorem source_gram_19_7_11 : Z 19 7 11 = (-75442752000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_11

theorem source_gram_19_7_13 : Z 19 7 13 = (-1225944720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_13

theorem source_gram_19_7_15 : Z 19 7 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_15

theorem source_gram_19_7_17 : Z 19 7 17 = (29177484336000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_17

theorem source_gram_19_7_19 : Z 19 7 19 = (118794043368000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_7_19

theorem source_gram_19_9_9 : Z 19 9 9 = (1265380704000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_9

theorem source_gram_19_9_11 : Z 19 9 11 = (-678984768000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_11

theorem source_gram_19_9_13 : Z 19 9 13 = (-1103350248000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_13

theorem source_gram_19_9_15 : Z 19 9 15 = (2574483912000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_15

theorem source_gram_19_9_17 : Z 19 9 17 = (9378477108000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_17

theorem source_gram_19_9_19 : Z 19 9 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_9_19

theorem source_gram_19_11_11 : Z 19 11 11 = (572107536000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_11_11

theorem source_gram_19_11_13 : Z 19 11 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_11_13

theorem source_gram_19_11_15 : Z 19 11 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_11_15

theorem source_gram_19_11_17 : Z 19 11 17 = (-7641722088000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_11_17

theorem source_gram_19_11_19 : Z 19 11 19 = (-29698510842000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_11_19

theorem source_gram_19_13_13 : Z 19 13 13 = (3544293753000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_13_13

theorem source_gram_19_13_15 : Z 19 13 15 = (-6574128561000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_13_15

theorem source_gram_19_13_17 : Z 19 13 17 = (-16933361445000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_13_17

theorem source_gram_19_13_19 : Z 19 13 19 = (-29698510842000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_13_19

theorem source_gram_19_15_15 : Z 19 15 15 = (17439063642000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_15_15

theorem source_gram_19_15_17 : Z 19 15 17 = (-19538493975000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_15_17

theorem source_gram_19_15_19 : Z 19 15 19 = (-22273883131500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_15_19

theorem source_gram_19_17_17 : Z 19 17 17 = (693290894546250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_17_17

theorem source_gram_19_17_19 : Z 19 17 19 = (-14849255421000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_17_19

theorem source_gram_19_19_19 : Z 19 19 19 = (121635819624193875 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_19_19_19

theorem source_gram_19_3_1 : Z 19 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_3

theorem source_gram_19_5_1 : Z 19 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_5

theorem source_gram_19_5_3 : Z 19 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_5

theorem source_gram_19_7_1 : Z 19 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_7

theorem source_gram_19_7_3 : Z 19 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_7

theorem source_gram_19_7_5 : Z 19 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_7

theorem source_gram_19_9_1 : Z 19 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_9

theorem source_gram_19_9_3 : Z 19 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_9

theorem source_gram_19_9_5 : Z 19 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_9

theorem source_gram_19_9_7 : Z 19 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_9

theorem source_gram_19_11_1 : Z 19 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_11

theorem source_gram_19_11_3 : Z 19 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_11

theorem source_gram_19_11_5 : Z 19 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_11

theorem source_gram_19_11_7 : Z 19 11 7 = (-75442752000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_11

theorem source_gram_19_11_9 : Z 19 11 9 = (-678984768000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_9_11

theorem source_gram_19_13_1 : Z 19 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_13

theorem source_gram_19_13_3 : Z 19 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_13

theorem source_gram_19_13_5 : Z 19 13 5 = (-245188944000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_13

theorem source_gram_19_13_7 : Z 19 13 7 = (-1225944720000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_13

theorem source_gram_19_13_9 : Z 19 13 9 = (-1103350248000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_9_13

theorem source_gram_19_13_11 : Z 19 13 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_11_13

theorem source_gram_19_15_1 : Z 19 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_15

theorem source_gram_19_15_3 : Z 19 15 3 = (-1961511552000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_15

theorem source_gram_19_15_5 : Z 19 15 5 = (-3677834160000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_15

theorem source_gram_19_15_7 : Z 19 15 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_15

theorem source_gram_19_15_9 : Z 19 15 9 = (2574483912000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_9_15

theorem source_gram_19_15_11 : Z 19 15 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_11_15

theorem source_gram_19_15_13 : Z 19 15 13 = (-6574128561000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_13_15

theorem source_gram_19_17_1 : Z 19 17 1 = (-50018544576000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_17

theorem source_gram_19_17_3 : Z 19 17 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_17

theorem source_gram_19_17_5 : Z 19 17 5 = (34735100400000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_17

theorem source_gram_19_17_7 : Z 19 17 7 = (29177484336000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_17

theorem source_gram_19_17_9 : Z 19 17 9 = (9378477108000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_9_17

theorem source_gram_19_17_11 : Z 19 17 11 = (-7641722088000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_11_17

theorem source_gram_19_17_13 : Z 19 17 13 = (-16933361445000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_13_17

theorem source_gram_19_17_15 : Z 19 17 15 = (-19538493975000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_15_17

theorem source_gram_19_19_1 : Z 19 19 1 = (3801409387776000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_1_19

theorem source_gram_19_19_3 : Z 19 19 3 = (1425528520416000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_3_19

theorem source_gram_19_19_5 : Z 19 19 5 = (475176173472000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_5_19

theorem source_gram_19_19_7 : Z 19 19 7 = (118794043368000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_7_19

theorem source_gram_19_19_9 : Z 19 19 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_9_19

theorem source_gram_19_19_11 : Z 19 19 11 = (-29698510842000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_11_19

theorem source_gram_19_19_13 : Z 19 19 13 = (-29698510842000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_13_19

theorem source_gram_19_19_15 : Z 19 19 15 = (-22273883131500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_15_19

theorem source_gram_19_19_17 : Z 19 19 17 = (-14849255421000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_19_17_19

theorem gram_19 : gramRational 19 = candidateZ_19 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_19_1_1
  · exact source_gram_19_1_3
  · exact source_gram_19_1_5
  · exact source_gram_19_1_7
  · exact source_gram_19_1_9
  · exact source_gram_19_1_11
  · exact source_gram_19_1_13
  · exact source_gram_19_1_15
  · exact source_gram_19_1_17
  · exact source_gram_19_1_19
  · exact source_gram_19_3_1
  · exact source_gram_19_3_3
  · exact source_gram_19_3_5
  · exact source_gram_19_3_7
  · exact source_gram_19_3_9
  · exact source_gram_19_3_11
  · exact source_gram_19_3_13
  · exact source_gram_19_3_15
  · exact source_gram_19_3_17
  · exact source_gram_19_3_19
  · exact source_gram_19_5_1
  · exact source_gram_19_5_3
  · exact source_gram_19_5_5
  · exact source_gram_19_5_7
  · exact source_gram_19_5_9
  · exact source_gram_19_5_11
  · exact source_gram_19_5_13
  · exact source_gram_19_5_15
  · exact source_gram_19_5_17
  · exact source_gram_19_5_19
  · exact source_gram_19_7_1
  · exact source_gram_19_7_3
  · exact source_gram_19_7_5
  · exact source_gram_19_7_7
  · exact source_gram_19_7_9
  · exact source_gram_19_7_11
  · exact source_gram_19_7_13
  · exact source_gram_19_7_15
  · exact source_gram_19_7_17
  · exact source_gram_19_7_19
  · exact source_gram_19_9_1
  · exact source_gram_19_9_3
  · exact source_gram_19_9_5
  · exact source_gram_19_9_7
  · exact source_gram_19_9_9
  · exact source_gram_19_9_11
  · exact source_gram_19_9_13
  · exact source_gram_19_9_15
  · exact source_gram_19_9_17
  · exact source_gram_19_9_19
  · exact source_gram_19_11_1
  · exact source_gram_19_11_3
  · exact source_gram_19_11_5
  · exact source_gram_19_11_7
  · exact source_gram_19_11_9
  · exact source_gram_19_11_11
  · exact source_gram_19_11_13
  · exact source_gram_19_11_15
  · exact source_gram_19_11_17
  · exact source_gram_19_11_19
  · exact source_gram_19_13_1
  · exact source_gram_19_13_3
  · exact source_gram_19_13_5
  · exact source_gram_19_13_7
  · exact source_gram_19_13_9
  · exact source_gram_19_13_11
  · exact source_gram_19_13_13
  · exact source_gram_19_13_15
  · exact source_gram_19_13_17
  · exact source_gram_19_13_19
  · exact source_gram_19_15_1
  · exact source_gram_19_15_3
  · exact source_gram_19_15_5
  · exact source_gram_19_15_7
  · exact source_gram_19_15_9
  · exact source_gram_19_15_11
  · exact source_gram_19_15_13
  · exact source_gram_19_15_15
  · exact source_gram_19_15_17
  · exact source_gram_19_15_19
  · exact source_gram_19_17_1
  · exact source_gram_19_17_3
  · exact source_gram_19_17_5
  · exact source_gram_19_17_7
  · exact source_gram_19_17_9
  · exact source_gram_19_17_11
  · exact source_gram_19_17_13
  · exact source_gram_19_17_15
  · exact source_gram_19_17_17
  · exact source_gram_19_17_19
  · exact source_gram_19_19_1
  · exact source_gram_19_19_3
  · exact source_gram_19_19_5
  · exact source_gram_19_19_7
  · exact source_gram_19_19_9
  · exact source_gram_19_19_11
  · exact source_gram_19_19_13
  · exact source_gram_19_19_15
  · exact source_gram_19_19_17
  · exact source_gram_19_19_19

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_19 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_19_0_0
  · exact computeLDL_19_0_1
  · exact computeLDL_19_0_2
  · exact computeLDL_19_0_3
  · exact computeLDL_19_0_4
  · exact computeLDL_19_0_5
  · exact computeLDL_19_0_6
  · exact computeLDL_19_0_7
  · exact computeLDL_19_0_8
  · exact computeLDL_19_0_9
  · exact computeLDL_19_1_0
  · exact computeLDL_19_1_1
  · exact computeLDL_19_1_2
  · exact computeLDL_19_1_3
  · exact computeLDL_19_1_4
  · exact computeLDL_19_1_5
  · exact computeLDL_19_1_6
  · exact computeLDL_19_1_7
  · exact computeLDL_19_1_8
  · exact computeLDL_19_1_9
  · exact computeLDL_19_2_0
  · exact computeLDL_19_2_1
  · exact computeLDL_19_2_2
  · exact computeLDL_19_2_3
  · exact computeLDL_19_2_4
  · exact computeLDL_19_2_5
  · exact computeLDL_19_2_6
  · exact computeLDL_19_2_7
  · exact computeLDL_19_2_8
  · exact computeLDL_19_2_9
  · exact computeLDL_19_3_0
  · exact computeLDL_19_3_1
  · exact computeLDL_19_3_2
  · exact computeLDL_19_3_3
  · exact computeLDL_19_3_4
  · exact computeLDL_19_3_5
  · exact computeLDL_19_3_6
  · exact computeLDL_19_3_7
  · exact computeLDL_19_3_8
  · exact computeLDL_19_3_9
  · exact computeLDL_19_4_0
  · exact computeLDL_19_4_1
  · exact computeLDL_19_4_2
  · exact computeLDL_19_4_3
  · exact computeLDL_19_4_4
  · exact computeLDL_19_4_5
  · exact computeLDL_19_4_6
  · exact computeLDL_19_4_7
  · exact computeLDL_19_4_8
  · exact computeLDL_19_4_9
  · exact computeLDL_19_5_0
  · exact computeLDL_19_5_1
  · exact computeLDL_19_5_2
  · exact computeLDL_19_5_3
  · exact computeLDL_19_5_4
  · exact computeLDL_19_5_5
  · exact computeLDL_19_5_6
  · exact computeLDL_19_5_7
  · exact computeLDL_19_5_8
  · exact computeLDL_19_5_9
  · exact computeLDL_19_6_0
  · exact computeLDL_19_6_1
  · exact computeLDL_19_6_2
  · exact computeLDL_19_6_3
  · exact computeLDL_19_6_4
  · exact computeLDL_19_6_5
  · exact computeLDL_19_6_6
  · exact computeLDL_19_6_7
  · exact computeLDL_19_6_8
  · exact computeLDL_19_6_9
  · exact computeLDL_19_7_0
  · exact computeLDL_19_7_1
  · exact computeLDL_19_7_2
  · exact computeLDL_19_7_3
  · exact computeLDL_19_7_4
  · exact computeLDL_19_7_5
  · exact computeLDL_19_7_6
  · exact computeLDL_19_7_7
  · exact computeLDL_19_7_8
  · exact computeLDL_19_7_9
  · exact computeLDL_19_8_0
  · exact computeLDL_19_8_1
  · exact computeLDL_19_8_2
  · exact computeLDL_19_8_3
  · exact computeLDL_19_8_4
  · exact computeLDL_19_8_5
  · exact computeLDL_19_8_6
  · exact computeLDL_19_8_7
  · exact computeLDL_19_8_8
  · exact computeLDL_19_8_9
  · exact computeLDL_19_9_0
  · exact computeLDL_19_9_1
  · exact computeLDL_19_9_2
  · exact computeLDL_19_9_3
  · exact computeLDL_19_9_4
  · exact computeLDL_19_9_5
  · exact computeLDL_19_9_6
  · exact computeLDL_19_9_7
  · exact computeLDL_19_9_8
  · exact computeLDL_19_9_9

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_19 : compressedRational 19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  rw [compressedRational_eq_compute, error_19, gram_19]
  exact candidateLDL_19

theorem four_body_19_positive_oai :
    ((compressedRational 19).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_19 pivots_19 ldl_19
  intro i
  fin_cases i <;> norm_num [pivots_19]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_19_positive_oai := @OAI.Laughlin.Certificate.four_body_19_positive_oai
