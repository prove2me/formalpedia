-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_12_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:12:56.620933+00:00
-- url     : https://prove2.me/submissions/40810e74-21e4-412d-a3a8-2719ded4406b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_12

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_12 : GramCompute.quadruples 12 = [(0,1,2,10), (0,1,3,9), (0,1,4,8), (0,1,5,7), (0,2,3,8), (0,2,4,7), (0,2,5,6), (0,3,4,6), (1,2,3,7), (1,2,4,6), (1,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_1_1 : GramCompute.ZFast 12 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_3 : GramCompute.ZFast 12 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_5 : GramCompute.ZFast 12 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_7 : GramCompute.ZFast 12 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_9 : GramCompute.ZFast 12 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_11 : GramCompute.ZFast 12 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_3_3 : GramCompute.ZFast 12 3 3 = (2177280 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_5 : GramCompute.ZFast 12 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_7 : GramCompute.ZFast 12 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_9 : GramCompute.ZFast 12 3 9 = (-1088640 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_11 : GramCompute.ZFast 12 3 11 = (7484400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_5_5 : GramCompute.ZFast 12 5 5 = (604800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_7 : GramCompute.ZFast 12 5 7 = (-453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_9 : GramCompute.ZFast 12 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_11 : GramCompute.ZFast 12 5 11 = (2494800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_7_7 : GramCompute.ZFast 12 7 7 = (340200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_7_9 : GramCompute.ZFast 12 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_7_11 : GramCompute.ZFast 12 7 11 = (-1871100 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_9_9 : GramCompute.ZFast 12 9 9 = (544320 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_9_11 : GramCompute.ZFast 12 9 11 = (-3742200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram111112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_11_11 : GramCompute.ZFast 12 11 11 = (36018675 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch12
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch12
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

theorem computeLDL_12_1_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 1 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_2_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_2_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 2 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_3_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_3_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 3 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_4_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_4_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 4 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_12_5_0 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 0 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_1 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 1 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_2 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 2 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_3 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 3 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_4 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 4 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_12_5_5 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 5 5 =
    (lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose) 5 5 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_12_1_1 : Z 12 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_1

theorem source_gram_12_1_3 : Z 12 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_3

theorem source_gram_12_1_5 : Z 12 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_5

theorem source_gram_12_1_7 : Z 12 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_7

theorem source_gram_12_1_9 : Z 12 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_9

theorem source_gram_12_1_11 : Z 12 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_11

theorem source_gram_12_3_3 : Z 12 3 3 = (2177280 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_3

theorem source_gram_12_3_5 : Z 12 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_5

theorem source_gram_12_3_7 : Z 12 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_7

theorem source_gram_12_3_9 : Z 12 3 9 = (-1088640 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_9

theorem source_gram_12_3_11 : Z 12 3 11 = (7484400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_11

theorem source_gram_12_5_5 : Z 12 5 5 = (604800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_5

theorem source_gram_12_5_7 : Z 12 5 7 = (-453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_7

theorem source_gram_12_5_9 : Z 12 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_9

theorem source_gram_12_5_11 : Z 12 5 11 = (2494800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_11

theorem source_gram_12_7_7 : Z 12 7 7 = (340200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_7

theorem source_gram_12_7_9 : Z 12 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_9

theorem source_gram_12_7_11 : Z 12 7 11 = (-1871100 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_11

theorem source_gram_12_9_9 : Z 12 9 9 = (544320 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_9_9

theorem source_gram_12_9_11 : Z 12 9 11 = (-3742200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_9_11

theorem source_gram_12_11_11 : Z 12 11 11 = (36018675 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_11_11

theorem source_gram_12_3_1 : Z 12 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_3

theorem source_gram_12_5_1 : Z 12 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_5

theorem source_gram_12_5_3 : Z 12 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_5

theorem source_gram_12_7_1 : Z 12 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_7

theorem source_gram_12_7_3 : Z 12 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_7

theorem source_gram_12_7_5 : Z 12 7 5 = (-453600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_7

theorem source_gram_12_9_1 : Z 12 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_9

theorem source_gram_12_9_3 : Z 12 9 3 = (-1088640 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_9

theorem source_gram_12_9_5 : Z 12 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_9

theorem source_gram_12_9_7 : Z 12 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_7_9

theorem source_gram_12_11_1 : Z 12 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_11

theorem source_gram_12_11_3 : Z 12 11 3 = (7484400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_11

theorem source_gram_12_11_5 : Z 12 11 5 = (2494800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_11

theorem source_gram_12_11_7 : Z 12 11 7 = (-1871100 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_7_11

theorem source_gram_12_11_9 : Z 12 11 9 = (-3742200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_9_11

theorem gram_12 : gramRational 12 = candidateZ_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_12_1_1
  · exact source_gram_12_1_3
  · exact source_gram_12_1_5
  · exact source_gram_12_1_7
  · exact source_gram_12_1_9
  · exact source_gram_12_1_11
  · exact source_gram_12_3_1
  · exact source_gram_12_3_3
  · exact source_gram_12_3_5
  · exact source_gram_12_3_7
  · exact source_gram_12_3_9
  · exact source_gram_12_3_11
  · exact source_gram_12_5_1
  · exact source_gram_12_5_3
  · exact source_gram_12_5_5
  · exact source_gram_12_5_7
  · exact source_gram_12_5_9
  · exact source_gram_12_5_11
  · exact source_gram_12_7_1
  · exact source_gram_12_7_3
  · exact source_gram_12_7_5
  · exact source_gram_12_7_7
  · exact source_gram_12_7_9
  · exact source_gram_12_7_11
  · exact source_gram_12_9_1
  · exact source_gram_12_9_3
  · exact source_gram_12_9_5
  · exact source_gram_12_9_7
  · exact source_gram_12_9_9
  · exact source_gram_12_9_11
  · exact source_gram_12_11_1
  · exact source_gram_12_11_3
  · exact source_gram_12_11_5
  · exact source_gram_12_11_7
  · exact source_gram_12_11_9
  · exact source_gram_12_11_11

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_12 : MatrixCompute.compressed 12 candidateY_12 candidateZ_12 =
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
  · exact computeLDL_12_1_5
  · exact computeLDL_12_2_0
  · exact computeLDL_12_2_1
  · exact computeLDL_12_2_2
  · exact computeLDL_12_2_3
  · exact computeLDL_12_2_4
  · exact computeLDL_12_2_5
  · exact computeLDL_12_3_0
  · exact computeLDL_12_3_1
  · exact computeLDL_12_3_2
  · exact computeLDL_12_3_3
  · exact computeLDL_12_3_4
  · exact computeLDL_12_3_5
  · exact computeLDL_12_4_0
  · exact computeLDL_12_4_1
  · exact computeLDL_12_4_2
  · exact computeLDL_12_4_3
  · exact computeLDL_12_4_4
  · exact computeLDL_12_4_5
  · exact computeLDL_12_5_0
  · exact computeLDL_12_5_1
  · exact computeLDL_12_5_2
  · exact computeLDL_12_5_3
  · exact computeLDL_12_5_4
  · exact computeLDL_12_5_5

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_12 : compressedRational 12 =
    lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose := by
  rw [compressedRational_eq_compute, error_12, gram_12]
  exact candidateLDL_12

theorem four_body_12_positive_oai :
    ((compressedRational 12).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_12 pivots_12 ldl_12
  intro i
  fin_cases i <;> norm_num [pivots_12]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_12_positive_oai := @OAI.Laughlin.Certificate.four_body_12_positive_oai
