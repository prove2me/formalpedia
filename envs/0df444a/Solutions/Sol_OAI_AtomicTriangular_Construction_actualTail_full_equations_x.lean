-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualTail_full_equations_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:44.842954+00:00
-- url     : https://prove2.me/submissions/e78fec82-edb2-426a-9c23-28832095f129

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010
import Definitions.Def_OAIQ257X000
import Theorems.Thm_OAI_AtomicTriangular_Construction_Bkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_summable_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_summable_x
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

omit [Fintype n] in
lemma colNorm_nonneg (A : Matrix m n ℝ) (j : n) : 0 ≤ colNorm A j :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
lemma matNorm_nonneg [Nonempty n] (A : Matrix m n ℝ) : 0 ≤ matNorm A := by
  obtain ⟨j⟩ := ‹Nonempty n›
  exact (colNorm_nonneg A j).trans (colNorm_le_matNorm A j)
lemma matNorm_le [Nonempty n] {A : Matrix m n ℝ} {c : ℝ}
    (h : ∀ j, colNorm A j ≤ c) : matNorm A ≤ c := by
  classical
  exact (Finset.sup'_le_iff _ _).mpr (fun j _ => h j)
omit [Fintype n] in
lemma colNorm_add (A B : Matrix m n ℝ) (j : n) :
    colNorm (A+B) j ≤ colNorm A j + colNorm B j := by
  unfold colNorm
  simp only [Matrix.add_apply,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)
lemma matNorm_add [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A+B) ≤ matNorm A + matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_add A B j).trans (add_le_add (colNorm_le_matNorm A j) (colNorm_le_matNorm B j))
omit [Fintype n] in
lemma colNorm_neg (A : Matrix m n ℝ) (j : n) : colNorm (-A) j = colNorm A j := by
  simp only [colNorm,Matrix.neg_apply,abs_neg]
lemma matNorm_neg [Nonempty n] (A : Matrix m n ℝ) : matNorm (-A) = matNorm A := by
  simp only [matNorm,colNorm_neg]
lemma matNorm_sub [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A-B) ≤ matNorm A + matNorm B := by
  simpa only [sub_eq_add_neg,matNorm_neg] using matNorm_add A (-B)
omit [Fintype p] in
lemma colNorm_mul [Nonempty n] (A : Matrix m n ℝ) (B : Matrix n p ℝ) (j : p) :
    colNorm (A*B) j ≤ matNorm A * colNorm B j := by
  classical
  calc
    colNorm (A*B) j ≤ ∑ i, ∑ k, |A i k * B k j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k, colNorm A k * |B k j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ k, matNorm A * |B k j| := Finset.sum_le_sum
      (fun k _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A k) (abs_nonneg _))
    _ = matNorm A * colNorm B j := by simp only [colNorm,Finset.mul_sum]
lemma matNorm_mul [Nonempty n] [Nonempty p] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    matNorm (A*B) ≤ matNorm A * matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_mul A B j).trans (mul_le_mul_of_nonneg_left
    (colNorm_le_matNorm B j) (matNorm_nonneg A))

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
lemma inverse_bound_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (_hb : 0 ≤ b) (he1 : e < 1) :
    matNorm A⁻¹ ≤ b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹ = C-(C*A-1)*A⁻¹ := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  have hx : matNorm A⁻¹ ≤ b+e*matNorm A⁻¹ := by
    calc
      _ ≤ matNorm C + matNorm ((C*A-1)*A⁻¹) := by
        conv_lhs => rw [hid]
        exact matNorm_sub _ _
      _ ≤ b+e*matNorm A⁻¹ := add_le_add hc ((matNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right he (matNorm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr he1)).mpr
  nlinarith
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

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

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

lemma RI.mem_singleton (z : ℤ) : (RI.singleton z).Mem ((z:ℝ)/(scale:ℝ)) := by
  have hs : (scale:ℝ) ≠ 0 := scale_pos.ne'
  have hh : (scale:ℝ)*((z:ℝ)/(scale:ℝ)) = (z:ℝ) := by field_simp
  constructor <;> dsimp only [RI.Mem,RI.singleton] <;> rw [hh]

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
lemma minusApproxBox_mem (i j : Fin 20) : (minusApproxBox i j).Mem (minusApprox i j) := RI.mem_singleton _
lemma minusApprox_bound : matNorm minusApprox ≤ (16155/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 16155000000000000000000000000000000000000000000000000000000000) minusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
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
lemma minusInverse_bound : matNorm (1 - Construction.R)⁻¹ < (1616/100:ℝ) := by
  exact (inverse_bound_of_residual _ _ (16155/1000) ((1:ℝ)/10^26)
    minusApprox_bound minusResidual_bound (by norm_num) (by norm_num)).trans_lt (by norm_num)
lemma plusApproxBox_mem (i j : Fin 20) : (plusApproxBox i j).Mem (plusApprox i j) := RI.mem_singleton _
lemma plusApprox_bound : matNorm plusApprox ≤ (3885/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 3885000000000000000000000000000000000000000000000000000000000) plusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
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
lemma plusInverse_bound : matNorm (1 + Construction.R)⁻¹ < (389/100:ℝ) := by
  exact (inverse_bound_of_residual _ _ (3885/1000) ((1:ℝ)/10^26)
    plusApprox_bound plusResidual_bound (by norm_num) (by norm_num)).trans_lt (by norm_num)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology lp
namespace AtomicTriangular.L1Kernel
variable {α β : Type*}

variable (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|))
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ j, ∑' i, |K i j| ≤ C)
include C hB
include hC in
lemma operator_norm : ‖operator K hK C hB‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (applyKernel_norm K hK C hB)
end AtomicTriangular.L1Kernel
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
lemma l1Matrix_norm (A : Matrix m n ℝ) : ‖l1Matrix A‖ ≤ matNorm A :=
  operator_norm _ _ _ (matNorm_nonneg A) _
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
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
lemma Boperator_norm : ‖Boperator‖ ≤ 335 := operator_norm _ _ _ (by norm_num) _
lemma Coperator_norm : ‖Coperator‖ ≤ 7/10^15 := operator_norm _ _ _ (by norm_num) _
lemma Doperator_norm : ‖Doperator‖ ≤ 23/10^9 := operator_norm _ _ _ (by norm_num) _
lemma Lplus_norm : ‖Lplus‖ ≤ 17 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.minusInverse_bound).le.trans (by norm_num)
lemma Lminus_norm : ‖Lminus‖ ≤ 5 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.plusInverse_bound).le.trans (by norm_num)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma repetitionExpData_calc : repetitionExpInput.exp.re=repetitionExpData := by decide +kernel
lemma repetitionExpData_mem : repetitionExpData.Mem repetitionRatio := by
  rw [← repetitionExpData_calc]
  apply ri_exp_mem
  exact RI.mem_mul (RI.mem_mul (by simpa using RI.mem_point (-36)) piBox_mem)
    (by simpa [Construction.eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5))
  decide +kernel
lemma repetitionNormBox_calc :
    (((RI.point 1).add (piBox.mul ((RI.point 1).divNat 5))).mul repetitionExpData).mul
      (((RI.point 1).sub repetitionExpData).invPos)=repetitionNormBox := by decide +kernel
lemma repetitionNormBox_mem : repetitionNormBox.Mem repetitionNorm := by
  rw [← repetitionNormBox_calc]
  unfold repetitionNorm
  rw [div_eq_mul_inv]
  apply RI.mem_mul
  · apply RI.mem_mul
    · exact RI.mem_add ri1_mem (RI.mem_mul piBox_mem
        (by simpa [Construction.eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)))
    · exact repetitionExpData_mem
  · exact RI.mem_invPos (RI.mem_sub ri1_mem repetitionExpData_mem) (by decide +kernel)
lemma repetitionNorm_bound : repetitionNorm < (1/4000000000:ℝ) := by
  simpa using ri_mem_lt repetitionNormBox_mem 1 4000000000 (by norm_num) (by decide +kernel)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma repetitionNorm_nonneg : 0 ≤ repetitionNorm := by
  unfold repetitionNorm
  exact div_nonneg (mul_nonneg (by linarith [pi_eta_pos]) repetitionRatio_pos.le)
    (sub_pos.mpr repetitionRatio_lt).le
lemma Aoperator_norm : ‖Aoperator‖ ≤ repetitionNorm :=
  operator_norm _ _ _ repetitionNorm_nonneg _
lemma AC_bound : ‖Aoperator‖+‖Coperator‖ ≤ beta := by
  have hA := Aoperator_norm
  have hC := Coperator_norm
  have hr := repetitionNorm_bound
  norm_num [beta] at *
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma neumann_equation (T : F →L[ℝ] F) (hT : ‖T‖<1) (y : F) :
    neumann T y - T (neumann T y) = y := by
  have hh := congrArg (fun A : F →L[ℝ] F => A y) (mul_neg_geom_series T hT)
  simpa only [neumann,sub_apply,mul_apply_eq_comp,
    one_apply_eq_self] using hh
omit [CompleteSpace E] in
lemma solution_equations (L : E →L[ℝ] E) (B : F →L[ℝ] E) (K : E →L[ℝ] F)
    (D : F →L[ℝ] F) (r : E) (s : F) (h : ‖tailOperator L B K D‖<1) :
    tailSolution L B K D r s = D (tailSolution L B K D r s)+
      K (finiteSolution L B K D r s)+s := by
  have hh := neumann_equation (tailOperator L B K D) h (s+K (L r))
  change tailSolution L B K D r s - _ = _ at hh
  simp only [tailOperator,add_apply,ContinuousLinearMap.comp_apply] at hh
  simp only [finiteSolution,map_add]
  rw [sub_eq_iff_eq_add] at hh
  calc
    _ = s+K (L r)+(D (tailSolution L B K D r s)+K (L (B (tailSolution L B K D r s)))) := hh
    _ = _ := by abel
end AtomicTriangular.Schur
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

lemma splitL_norm (e : Fin 2) : ‖splitL e‖ ≤ splitN e := by
  fin_cases e
  · exact Lplus_norm
  · exact Lminus_norm
lemma splitB_norm (e : Fin 2) : ‖splitB e‖ ≤ 340 := by
  have hh := Boperator_norm
  fin_cases e <;> simp only [splitB,↓reduceIte,Nat.one_ne_zero,norm_neg] <;> linarith
lemma splitK_norm (e : Fin 2) : ‖splitK e‖ ≤ beta := by
  have ha := AC_bound
  fin_cases e
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using (show ‖Coperator‖+‖Aoperator‖≤beta by linarith))
lemma splitD_norm (e : Fin 2) : ‖splitD e‖ ≤ delta := by
  have hh := Doperator_norm
  fin_cases e <;> simp only [splitD,↓reduceIte,Nat.one_ne_zero,norm_neg] <;>
    norm_num [delta] at * <;> linarith
lemma splitN_nonneg (e : Fin 2) : 0 ≤ splitN e := by fin_cases e <;> (first | (simp [splitN]; all_goals first | (norm_num [splitN]; done) | rfl | decide) | (norm_num [splitN]; done) | norm_num [splitN])
lemma splitQ_lt (e : Fin 2) : splitQ e<1 := by fin_cases e <;> (first | (simp [splitQ,splitN,beta,delta]; all_goals first | (norm_num [splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [splitQ,splitN,beta,delta]; done) | norm_num [splitQ,splitN,beta,delta])
lemma splitOperator_norm (e : Fin 2) :
    ‖tailOperator (splitL e) (splitB e) (splitK e) (splitD e)‖ ≤ splitQ e := by
  have hb : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖splitD e‖+‖(splitK e).comp ((splitL e).comp (splitB e))‖ := norm_add_le _ _
    _ ≤ delta+‖splitK e‖*(‖splitL e‖*‖splitB e‖) :=
      add_le_add (splitD_norm e) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
    _ ≤ delta+beta*(splitN e*340) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
      · exact splitB_norm e
    _ = splitQ e := by unfold splitQ; ring

lemma correctionTail_equation (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionTail e r s = splitD e (correctionTail e r s) +
      splitK e (correctionFinite e r s)+s :=
  solution_equations _ _ _ _ _ _ ((splitOperator_norm e).trans_lt (splitQ_lt e))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma actualTail_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+Coperator (actualFiniteError 1 z hz hzB)-
      Aoperator (actualFiniteError 0 z hz hzB)+tailTarget z hz hzB+
      CallOperator (finiteApprox 1 (actualParameter z))-AallOperator (finiteApprox 0 (actualParameter z))+
      (3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+Coperator (actualFiniteError 0 z hz hzB)-
      Aoperator (actualFiniteError 1 z hz hzB)+
      CallOperator (finiteApprox 0 (actualParameter z))-AallOperator (finiteApprox 1 (actualParameter z))-
      (3/500:ℝ) • tailFixedColumn 22 := by
  have hp := correctionTail_equation 0 (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionTail_equation 1 (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualTailSplit 0 z hz hzB=Doperator (actualTailSplit 0 z hz hzB)+
    (Coperator-Aoperator) (actualFiniteSplit 0 z hz hzB)+approximationTailResidual 0 z hz hzB at hp
  change actualTailSplit 1 z hz hzB=(-Doperator) (actualTailSplit 1 z hz hzB)+
    (-Coperator-Aoperator) (actualFiniteSplit 1 z hz hzB)+approximationTailResidual 1 z hz hzB at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : TailCoefficients => u i) hp
    have hm' := congrArg (fun u : TailCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,approximationTailResidual,
      Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_sub,map_neg,sub_apply,neg_apply,
      lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
lemma CallOperator_extend (u : FiniteCoefficients) :
    CallOperator (extendFiniteError u)=Coperator u := by
  ext p
  unfold CallOperator Coperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*CallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
lemma AallOperator_extend (u : FiniteCoefficients) :
    AallOperator (extendFiniteError u)=Aoperator u := by
  ext p
  unfold AallOperator Aoperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*AallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
  unfold AallKernel Akernel
  congr 1 <;> apply Fin.ext <;> dsimp <;> omega
lemma actualTail_full_equations_x_oai {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+
      CallOperator (actualTrigonometric 1 z hz hzB)-AallOperator (actualTrigonometric 0 z hz hzB)+
      tailTarget z hz hzB+(3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+
      CallOperator (actualTrigonometric 0 z hz hzB)-AallOperator (actualTrigonometric 1 z hz hzB)-
      (3/500:ℝ) • tailFixedColumn 22 := by
  rcases actualTail_equations hz hzB with ⟨h0,h1⟩
  simp only [actualTrigonometric,map_add,CallOperator_extend,AallOperator_extend]
  constructor
  · rw [h0]; abel
  · rw [h1]; abel
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualTail_full_equations_x_oai := @OAI.AtomicTriangular.Construction.actualTail_full_equations_x_oai
