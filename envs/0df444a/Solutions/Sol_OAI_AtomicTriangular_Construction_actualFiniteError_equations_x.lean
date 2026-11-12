-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualFiniteError_equations_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:43.580017+00:00
-- url     : https://prove2.me/submissions/5e2e280a-5f24-49a3-af15-1744d9e04f81

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusResidualBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_plusResidualBox_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_MatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma matNorm_le [Nonempty n] {A : Matrix m n ℝ} {c : ℝ}
    (h : ∀ j, colNorm A j ≤ c) : matNorm A ≤ c := by
  classical
  exact (Finset.sup'_le_iff _ _).mpr (fun j _ => h j)

end AtomicTriangular.MatrixBounds

namespace AtomicTriangular.MatrixBounds
open Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_nonneg (v : n → ℝ) : 0 ≤ vecNorm v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_zero_iff (v : n → ℝ) : vecNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi : |v i| ≤ vecNorm v := (Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    rw [h] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl; simp [vecNorm]
omit [DecidableEq n] in
lemma matrix_vecNorm (A : Matrix n n ℝ) (v : n → ℝ) :
    vecNorm (A.mulVec v) ≤ matNorm A * vecNorm v := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * v j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, colNorm A j * |v j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ j, matNorm A * |v j| := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A j) (abs_nonneg _))
    _ = _ := by simp only [vecNorm,Finset.mul_sum]
lemma isUnit_of_residual (A C : Matrix n n ℝ) (he : matNorm (C*A-1) < 1) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hh
  have hzero : A.mulVec (v-w) = 0 := by rw [mulVec_sub,hh,sub_self]
  have hres : (C*A-1).mulVec (v-w) = -(v-w) := by
    rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec, hzero,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
  have hb := matrix_vecNorm (C*A-1) (v-w)
  rw [hres] at hb
  have hneg : vecNorm (-(v-w)) = vecNorm (v-w) := by simp only [vecNorm, Pi.neg_apply, abs_neg]
  rw [hneg] at hb
  have hz := vecNorm_nonneg (v-w)
  have hv : vecNorm (v-w) = 0 := by nlinarith
  exact sub_eq_zero.mp ((vecNorm_zero_iff _).mp hv)
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

end
end AtomicTriangular.Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
lemma matrixNorm_bound [Nonempty n] {a : m → n → RI} {A : Matrix m n ℝ} {b : ℤ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ j, matrixColBound a j ≤ b) :
    matNorm A ≤ (b:ℝ)/(scale:ℝ) := by
  apply matNorm_le
  intro j
  have hh := (RI.mem_sum (fun i => RI.mem_abs (ha i j))).2
  apply (le_div_iff₀ scale_pos).mpr
  change colNorm A j * (scale:ℝ) ≤ (b:ℝ)
  rw [mul_comm]
  apply hh.trans
  exact_mod_cast hb j

end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma minusResidualRow0_calc (j : Fin 20) : minusResidualBox 0 j = minusResidualRow0 j := by
  revert j
  decide +kernel
lemma minusResidualRow0_mem (j : Fin 20) :
    (minusResidualRow0 j).Mem ((minusApprox*(1 - Construction.R)-1) 0 j) := by
  rw [← minusResidualRow0_calc]
  exact minusResidualBox_mem_x 0 j
lemma minusResidualRow1_calc (j : Fin 20) : minusResidualBox 1 j = minusResidualRow1 j := by
  revert j
  decide +kernel
lemma minusResidualRow1_mem (j : Fin 20) :
    (minusResidualRow1 j).Mem ((minusApprox*(1 - Construction.R)-1) 1 j) := by
  rw [← minusResidualRow1_calc]
  exact minusResidualBox_mem_x 1 j
lemma minusResidualRow2_calc (j : Fin 20) : minusResidualBox 2 j = minusResidualRow2 j := by
  revert j
  decide +kernel
lemma minusResidualRow2_mem (j : Fin 20) :
    (minusResidualRow2 j).Mem ((minusApprox*(1 - Construction.R)-1) 2 j) := by
  rw [← minusResidualRow2_calc]
  exact minusResidualBox_mem_x 2 j
lemma minusResidualRow3_calc (j : Fin 20) : minusResidualBox 3 j = minusResidualRow3 j := by
  revert j
  decide +kernel
lemma minusResidualRow3_mem (j : Fin 20) :
    (minusResidualRow3 j).Mem ((minusApprox*(1 - Construction.R)-1) 3 j) := by
  rw [← minusResidualRow3_calc]
  exact minusResidualBox_mem_x 3 j
lemma minusResidualRow4_calc (j : Fin 20) : minusResidualBox 4 j = minusResidualRow4 j := by
  revert j
  decide +kernel
lemma minusResidualRow4_mem (j : Fin 20) :
    (minusResidualRow4 j).Mem ((minusApprox*(1 - Construction.R)-1) 4 j) := by
  rw [← minusResidualRow4_calc]
  exact minusResidualBox_mem_x 4 j
lemma minusResidualRow5_calc (j : Fin 20) : minusResidualBox 5 j = minusResidualRow5 j := by
  revert j
  decide +kernel
lemma minusResidualRow5_mem (j : Fin 20) :
    (minusResidualRow5 j).Mem ((minusApprox*(1 - Construction.R)-1) 5 j) := by
  rw [← minusResidualRow5_calc]
  exact minusResidualBox_mem_x 5 j
lemma minusResidualRow6_calc (j : Fin 20) : minusResidualBox 6 j = minusResidualRow6 j := by
  revert j
  decide +kernel
lemma minusResidualRow6_mem (j : Fin 20) :
    (minusResidualRow6 j).Mem ((minusApprox*(1 - Construction.R)-1) 6 j) := by
  rw [← minusResidualRow6_calc]
  exact minusResidualBox_mem_x 6 j
lemma minusResidualRow7_calc (j : Fin 20) : minusResidualBox 7 j = minusResidualRow7 j := by
  revert j
  decide +kernel
lemma minusResidualRow7_mem (j : Fin 20) :
    (minusResidualRow7 j).Mem ((minusApprox*(1 - Construction.R)-1) 7 j) := by
  rw [← minusResidualRow7_calc]
  exact minusResidualBox_mem_x 7 j
lemma minusResidualRow8_calc (j : Fin 20) : minusResidualBox 8 j = minusResidualRow8 j := by
  revert j
  decide +kernel
lemma minusResidualRow8_mem (j : Fin 20) :
    (minusResidualRow8 j).Mem ((minusApprox*(1 - Construction.R)-1) 8 j) := by
  rw [← minusResidualRow8_calc]
  exact minusResidualBox_mem_x 8 j
lemma minusResidualRow9_calc (j : Fin 20) : minusResidualBox 9 j = minusResidualRow9 j := by
  revert j
  decide +kernel
lemma minusResidualRow9_mem (j : Fin 20) :
    (minusResidualRow9 j).Mem ((minusApprox*(1 - Construction.R)-1) 9 j) := by
  rw [← minusResidualRow9_calc]
  exact minusResidualBox_mem_x 9 j
lemma minusResidualRow10_calc (j : Fin 20) : minusResidualBox 10 j = minusResidualRow10 j := by
  revert j
  decide +kernel
lemma minusResidualRow10_mem (j : Fin 20) :
    (minusResidualRow10 j).Mem ((minusApprox*(1 - Construction.R)-1) 10 j) := by
  rw [← minusResidualRow10_calc]
  exact minusResidualBox_mem_x 10 j
lemma minusResidualRow11_calc (j : Fin 20) : minusResidualBox 11 j = minusResidualRow11 j := by
  revert j
  decide +kernel
lemma minusResidualRow11_mem (j : Fin 20) :
    (minusResidualRow11 j).Mem ((minusApprox*(1 - Construction.R)-1) 11 j) := by
  rw [← minusResidualRow11_calc]
  exact minusResidualBox_mem_x 11 j
lemma minusResidualRow12_calc (j : Fin 20) : minusResidualBox 12 j = minusResidualRow12 j := by
  revert j
  decide +kernel
lemma minusResidualRow12_mem (j : Fin 20) :
    (minusResidualRow12 j).Mem ((minusApprox*(1 - Construction.R)-1) 12 j) := by
  rw [← minusResidualRow12_calc]
  exact minusResidualBox_mem_x 12 j
lemma minusResidualRow13_calc (j : Fin 20) : minusResidualBox 13 j = minusResidualRow13 j := by
  revert j
  decide +kernel
lemma minusResidualRow13_mem (j : Fin 20) :
    (minusResidualRow13 j).Mem ((minusApprox*(1 - Construction.R)-1) 13 j) := by
  rw [← minusResidualRow13_calc]
  exact minusResidualBox_mem_x 13 j
lemma minusResidualRow14_calc (j : Fin 20) : minusResidualBox 14 j = minusResidualRow14 j := by
  revert j
  decide +kernel
lemma minusResidualRow14_mem (j : Fin 20) :
    (minusResidualRow14 j).Mem ((minusApprox*(1 - Construction.R)-1) 14 j) := by
  rw [← minusResidualRow14_calc]
  exact minusResidualBox_mem_x 14 j
lemma minusResidualRow15_calc (j : Fin 20) : minusResidualBox 15 j = minusResidualRow15 j := by
  revert j
  decide +kernel
lemma minusResidualRow15_mem (j : Fin 20) :
    (minusResidualRow15 j).Mem ((minusApprox*(1 - Construction.R)-1) 15 j) := by
  rw [← minusResidualRow15_calc]
  exact minusResidualBox_mem_x 15 j
lemma minusResidualRow16_calc (j : Fin 20) : minusResidualBox 16 j = minusResidualRow16 j := by
  revert j
  decide +kernel
lemma minusResidualRow16_mem (j : Fin 20) :
    (minusResidualRow16 j).Mem ((minusApprox*(1 - Construction.R)-1) 16 j) := by
  rw [← minusResidualRow16_calc]
  exact minusResidualBox_mem_x 16 j
lemma minusResidualRow17_calc (j : Fin 20) : minusResidualBox 17 j = minusResidualRow17 j := by
  revert j
  decide +kernel
lemma minusResidualRow17_mem (j : Fin 20) :
    (minusResidualRow17 j).Mem ((minusApprox*(1 - Construction.R)-1) 17 j) := by
  rw [← minusResidualRow17_calc]
  exact minusResidualBox_mem_x 17 j
lemma minusResidualRow18_calc (j : Fin 20) : minusResidualBox 18 j = minusResidualRow18 j := by
  revert j
  decide +kernel
lemma minusResidualRow18_mem (j : Fin 20) :
    (minusResidualRow18 j).Mem ((minusApprox*(1 - Construction.R)-1) 18 j) := by
  rw [← minusResidualRow18_calc]
  exact minusResidualBox_mem_x 18 j
lemma minusResidualRow19_calc (j : Fin 20) : minusResidualBox 19 j = minusResidualRow19 j := by
  revert j
  decide +kernel
lemma minusResidualRow19_mem (j : Fin 20) :
    (minusResidualRow19 j).Mem ((minusApprox*(1 - Construction.R)-1) 19 j) := by
  rw [← minusResidualRow19_calc]
  exact minusResidualBox_mem_x 19 j
lemma minusResidualTable_mem (i j : Fin 20) :
    (minusResidualTable i j).Mem ((minusApprox*(1 - Construction.R)-1) i j) := by
  fin_cases i
  · exact minusResidualRow0_mem j
  · exact minusResidualRow1_mem j
  · exact minusResidualRow2_mem j
  · exact minusResidualRow3_mem j
  · exact minusResidualRow4_mem j
  · exact minusResidualRow5_mem j
  · exact minusResidualRow6_mem j
  · exact minusResidualRow7_mem j
  · exact minusResidualRow8_mem j
  · exact minusResidualRow9_mem j
  · exact minusResidualRow10_mem j
  · exact minusResidualRow11_mem j
  · exact minusResidualRow12_mem j
  · exact minusResidualRow13_mem j
  · exact minusResidualRow14_mem j
  · exact minusResidualRow15_mem j
  · exact minusResidualRow16_mem j
  · exact minusResidualRow17_mem j
  · exact minusResidualRow18_mem j
  · exact minusResidualRow19_mem j
lemma minusResidual_bound : matNorm (minusApprox*(1 - Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) minusResidualTable_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma minusBlock_isUnit : IsUnit (1 - Construction.R) :=
  isUnit_of_residual _ minusApprox (minusResidual_bound.trans_lt (by norm_num))
lemma plusResidualRow0_calc (j : Fin 20) : plusResidualBox 0 j = plusResidualRow0 j := by
  revert j
  decide +kernel
lemma plusResidualRow0_mem (j : Fin 20) :
    (plusResidualRow0 j).Mem ((plusApprox*(1 + Construction.R)-1) 0 j) := by
  rw [← plusResidualRow0_calc]
  exact plusResidualBox_mem_x 0 j
lemma plusResidualRow1_calc (j : Fin 20) : plusResidualBox 1 j = plusResidualRow1 j := by
  revert j
  decide +kernel
lemma plusResidualRow1_mem (j : Fin 20) :
    (plusResidualRow1 j).Mem ((plusApprox*(1 + Construction.R)-1) 1 j) := by
  rw [← plusResidualRow1_calc]
  exact plusResidualBox_mem_x 1 j
lemma plusResidualRow2_calc (j : Fin 20) : plusResidualBox 2 j = plusResidualRow2 j := by
  revert j
  decide +kernel
lemma plusResidualRow2_mem (j : Fin 20) :
    (plusResidualRow2 j).Mem ((plusApprox*(1 + Construction.R)-1) 2 j) := by
  rw [← plusResidualRow2_calc]
  exact plusResidualBox_mem_x 2 j
lemma plusResidualRow3_calc (j : Fin 20) : plusResidualBox 3 j = plusResidualRow3 j := by
  revert j
  decide +kernel
lemma plusResidualRow3_mem (j : Fin 20) :
    (plusResidualRow3 j).Mem ((plusApprox*(1 + Construction.R)-1) 3 j) := by
  rw [← plusResidualRow3_calc]
  exact plusResidualBox_mem_x 3 j
lemma plusResidualRow4_calc (j : Fin 20) : plusResidualBox 4 j = plusResidualRow4 j := by
  revert j
  decide +kernel
lemma plusResidualRow4_mem (j : Fin 20) :
    (plusResidualRow4 j).Mem ((plusApprox*(1 + Construction.R)-1) 4 j) := by
  rw [← plusResidualRow4_calc]
  exact plusResidualBox_mem_x 4 j
lemma plusResidualRow5_calc (j : Fin 20) : plusResidualBox 5 j = plusResidualRow5 j := by
  revert j
  decide +kernel
lemma plusResidualRow5_mem (j : Fin 20) :
    (plusResidualRow5 j).Mem ((plusApprox*(1 + Construction.R)-1) 5 j) := by
  rw [← plusResidualRow5_calc]
  exact plusResidualBox_mem_x 5 j
lemma plusResidualRow6_calc (j : Fin 20) : plusResidualBox 6 j = plusResidualRow6 j := by
  revert j
  decide +kernel
lemma plusResidualRow6_mem (j : Fin 20) :
    (plusResidualRow6 j).Mem ((plusApprox*(1 + Construction.R)-1) 6 j) := by
  rw [← plusResidualRow6_calc]
  exact plusResidualBox_mem_x 6 j
lemma plusResidualRow7_calc (j : Fin 20) : plusResidualBox 7 j = plusResidualRow7 j := by
  revert j
  decide +kernel
lemma plusResidualRow7_mem (j : Fin 20) :
    (plusResidualRow7 j).Mem ((plusApprox*(1 + Construction.R)-1) 7 j) := by
  rw [← plusResidualRow7_calc]
  exact plusResidualBox_mem_x 7 j
lemma plusResidualRow8_calc (j : Fin 20) : plusResidualBox 8 j = plusResidualRow8 j := by
  revert j
  decide +kernel
lemma plusResidualRow8_mem (j : Fin 20) :
    (plusResidualRow8 j).Mem ((plusApprox*(1 + Construction.R)-1) 8 j) := by
  rw [← plusResidualRow8_calc]
  exact plusResidualBox_mem_x 8 j
lemma plusResidualRow9_calc (j : Fin 20) : plusResidualBox 9 j = plusResidualRow9 j := by
  revert j
  decide +kernel
lemma plusResidualRow9_mem (j : Fin 20) :
    (plusResidualRow9 j).Mem ((plusApprox*(1 + Construction.R)-1) 9 j) := by
  rw [← plusResidualRow9_calc]
  exact plusResidualBox_mem_x 9 j
lemma plusResidualRow10_calc (j : Fin 20) : plusResidualBox 10 j = plusResidualRow10 j := by
  revert j
  decide +kernel
lemma plusResidualRow10_mem (j : Fin 20) :
    (plusResidualRow10 j).Mem ((plusApprox*(1 + Construction.R)-1) 10 j) := by
  rw [← plusResidualRow10_calc]
  exact plusResidualBox_mem_x 10 j
lemma plusResidualRow11_calc (j : Fin 20) : plusResidualBox 11 j = plusResidualRow11 j := by
  revert j
  decide +kernel
lemma plusResidualRow11_mem (j : Fin 20) :
    (plusResidualRow11 j).Mem ((plusApprox*(1 + Construction.R)-1) 11 j) := by
  rw [← plusResidualRow11_calc]
  exact plusResidualBox_mem_x 11 j
lemma plusResidualRow12_calc (j : Fin 20) : plusResidualBox 12 j = plusResidualRow12 j := by
  revert j
  decide +kernel
lemma plusResidualRow12_mem (j : Fin 20) :
    (plusResidualRow12 j).Mem ((plusApprox*(1 + Construction.R)-1) 12 j) := by
  rw [← plusResidualRow12_calc]
  exact plusResidualBox_mem_x 12 j
lemma plusResidualRow13_calc (j : Fin 20) : plusResidualBox 13 j = plusResidualRow13 j := by
  revert j
  decide +kernel
lemma plusResidualRow13_mem (j : Fin 20) :
    (plusResidualRow13 j).Mem ((plusApprox*(1 + Construction.R)-1) 13 j) := by
  rw [← plusResidualRow13_calc]
  exact plusResidualBox_mem_x 13 j
lemma plusResidualRow14_calc (j : Fin 20) : plusResidualBox 14 j = plusResidualRow14 j := by
  revert j
  decide +kernel
lemma plusResidualRow14_mem (j : Fin 20) :
    (plusResidualRow14 j).Mem ((plusApprox*(1 + Construction.R)-1) 14 j) := by
  rw [← plusResidualRow14_calc]
  exact plusResidualBox_mem_x 14 j
lemma plusResidualRow15_calc (j : Fin 20) : plusResidualBox 15 j = plusResidualRow15 j := by
  revert j
  decide +kernel
lemma plusResidualRow15_mem (j : Fin 20) :
    (plusResidualRow15 j).Mem ((plusApprox*(1 + Construction.R)-1) 15 j) := by
  rw [← plusResidualRow15_calc]
  exact plusResidualBox_mem_x 15 j
lemma plusResidualRow16_calc (j : Fin 20) : plusResidualBox 16 j = plusResidualRow16 j := by
  revert j
  decide +kernel
lemma plusResidualRow16_mem (j : Fin 20) :
    (plusResidualRow16 j).Mem ((plusApprox*(1 + Construction.R)-1) 16 j) := by
  rw [← plusResidualRow16_calc]
  exact plusResidualBox_mem_x 16 j
lemma plusResidualRow17_calc (j : Fin 20) : plusResidualBox 17 j = plusResidualRow17 j := by
  revert j
  decide +kernel
lemma plusResidualRow17_mem (j : Fin 20) :
    (plusResidualRow17 j).Mem ((plusApprox*(1 + Construction.R)-1) 17 j) := by
  rw [← plusResidualRow17_calc]
  exact plusResidualBox_mem_x 17 j
lemma plusResidualRow18_calc (j : Fin 20) : plusResidualBox 18 j = plusResidualRow18 j := by
  revert j
  decide +kernel
lemma plusResidualRow18_mem (j : Fin 20) :
    (plusResidualRow18 j).Mem ((plusApprox*(1 + Construction.R)-1) 18 j) := by
  rw [← plusResidualRow18_calc]
  exact plusResidualBox_mem_x 18 j
lemma plusResidualRow19_calc (j : Fin 20) : plusResidualBox 19 j = plusResidualRow19 j := by
  revert j
  decide +kernel
lemma plusResidualRow19_mem (j : Fin 20) :
    (plusResidualRow19 j).Mem ((plusApprox*(1 + Construction.R)-1) 19 j) := by
  rw [← plusResidualRow19_calc]
  exact plusResidualBox_mem_x 19 j
lemma plusResidualTable_mem (i j : Fin 20) :
    (plusResidualTable i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) := by
  fin_cases i
  · exact plusResidualRow0_mem j
  · exact plusResidualRow1_mem j
  · exact plusResidualRow2_mem j
  · exact plusResidualRow3_mem j
  · exact plusResidualRow4_mem j
  · exact plusResidualRow5_mem j
  · exact plusResidualRow6_mem j
  · exact plusResidualRow7_mem j
  · exact plusResidualRow8_mem j
  · exact plusResidualRow9_mem j
  · exact plusResidualRow10_mem j
  · exact plusResidualRow11_mem j
  · exact plusResidualRow12_mem j
  · exact plusResidualRow13_mem j
  · exact plusResidualRow14_mem j
  · exact plusResidualRow15_mem j
  · exact plusResidualRow16_mem j
  · exact plusResidualRow17_mem j
  · exact plusResidualRow18_mem j
  · exact plusResidualRow19_mem j
lemma plusResidual_bound : matNorm (plusApprox*(1 + Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) plusResidualTable_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma plusBlock_isUnit : IsUnit (1 + Construction.R) :=
  isUnit_of_residual _ plusApprox (plusResidual_bound.trans_lt (by norm_num))

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.L1Kernel
lemma operator_apply {α β : Type*} (K : β → α → ℝ)
    (hK : ∀ j, Summable (fun i => |K i j|)) (C : ℝ)
    (hB : ∀ j, ∑' i, |K i j| ≤ C) (a : ℓ¹(α,ℝ)) (i : β) :
    operator K hK C hB a i = ∑' j, a j * K i j := by
  have hh := (lp.evalCLM ℝ (fun _ : β => ℝ) 1 i).map_tsum (summable_columns K hK C hB a)
  change (∑' j, a j • column K hK j) i = ∑' j, a j*K i j at ⊢
  change (∑' j, a j • column K hK j) i = ∑' j, (a j • column K hK j) i at hh
  simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,column] using hh
end AtomicTriangular.L1Kernel
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
omit [Nonempty m] in
lemma l1Matrix_apply (A : Matrix m n ℝ) (x : ℓ¹(n,ℝ)) (i : m) :
    l1Matrix A x i = ∑ j, A i j*x j := by
  have hh := operator_apply A (fun j => (hasSum_fintype _).summable) (matNorm A)
    (fun j => by simpa [tsum_fintype,colNorm] using colNorm_le_matNorm A j) x i
  simpa only [l1Matrix,tsum_fintype,mul_comm] using hh
omit [Nonempty m] in
lemma l1Matrix_mul (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    l1Matrix (A*B) = (l1Matrix A).comp (l1Matrix B) := by
  ext x i
  simp only [l1Matrix_apply,ContinuousLinearMap.comp_apply,Matrix.mul_apply,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma l1Matrix_one [DecidableEq n] : l1Matrix (1:Matrix n n ℝ) = 1 := by
  ext x i
  simp [l1Matrix_apply,Matrix.one_apply]
omit [Nonempty m] in
lemma l1Matrix_add (A B : Matrix m n ℝ) : l1Matrix (A+B)=l1Matrix A+l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,add_mul,Finset.sum_add_distrib]
omit [Nonempty m] in
lemma l1Matrix_sub (A B : Matrix m n ℝ) : l1Matrix (A-B)=l1Matrix A-l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,sub_mul,Finset.sum_sub_distrib]
lemma l1Matrix_inverse [DecidableEq n] (A : Matrix n n ℝ) (hA : IsUnit A) :
    (l1Matrix A).comp (l1Matrix A⁻¹)=1 ∧ (l1Matrix A⁻¹).comp (l1Matrix A)=1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor
  · rw [←l1Matrix_mul,Matrix.mul_nonsing_inv A hd,l1Matrix_one]
  · rw [←l1Matrix_mul,Matrix.nonsing_inv_mul A hd,l1Matrix_one]
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Lplus_left_inverse : (1-Roperator).comp Lplus=1 := by
  have hh := (l1Matrix_inverse (1-R) FiniteCertificate.minusBlock_isUnit).1
  simpa [Lplus,l1Matrix_sub,l1Matrix_one,Roperator] using hh
lemma Lminus_left_inverse : (1+Roperator).comp Lminus=1 := by
  have hh := (l1Matrix_inverse (1+R) FiniteCertificate.plusBlock_isUnit).1
  simpa [Lminus,l1Matrix_add,l1Matrix_one,Roperator] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma correctionFinite_plus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 0 r s = Roperator (correctionFinite 0 r s)+Boperator (correctionTail 0 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r+Boperator (correctionTail 0 r s))) Lplus_left_inverse
  change correctionFinite 0 r s-Roperator (correctionFinite 0 r s)=r+Boperator (correctionTail 0 r s) at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (by abel)
lemma correctionFinite_minus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 1 r s = -Roperator (correctionFinite 1 r s)-Boperator (correctionTail 1 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r-Boperator (correctionTail 1 r s))) Lminus_left_inverse
  change correctionFinite 1 r s+Roperator (correctionFinite 1 r s)=r-Boperator (correctionTail 1 r s) at hh
  exact eq_sub_of_add_eq hh |>.trans (by abel)
lemma actualFiniteError_equations_x_oai {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualFiniteError 0 z hz hzB = Roperator (actualFiniteError 1 z hz hzB)+Boperator (actualTail 1 z hz hzB)+finiteResidual z ∧
    actualFiniteError 1 z hz hzB = Roperator (actualFiniteError 0 z hz hzB)+Boperator (actualTail 0 z hz hzB) := by
  have hp := correctionFinite_plus (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionFinite_minus (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualFiniteSplit 0 z hz hzB=Roperator (actualFiniteSplit 0 z hz hzB)+Boperator (actualTailSplit 0 z hz hzB)+finiteResidual z at hp
  change actualFiniteSplit 1 z hz hzB= -Roperator (actualFiniteSplit 1 z hz hzB)-Boperator (actualTailSplit 1 z hz hzB)+finiteResidual z at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : FiniteCoefficients => u i) hp
    have hm' := congrArg (fun u : FiniteCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_neg,lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualFiniteError_equations_x_oai := @OAI.AtomicTriangular.Construction.actualFiniteError_equations_x_oai
