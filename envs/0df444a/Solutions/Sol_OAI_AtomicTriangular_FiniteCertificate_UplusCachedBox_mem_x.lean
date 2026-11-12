-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:51.528611+00:00
-- url     : https://prove2.me/submissions/c5fb53b6-d267-43d9-a5bb-a6587be0d0a1

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_R0Box_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusResidualTable_mem_x

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
lemma inverse_error_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (hb : 0 ≤ b) (he0 : 0 ≤ e) (he1 : e < 1) :
    matNorm (A⁻¹-C) ≤ e*b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹-C = -((C*A-1)*A⁻¹) := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  rw [hid,matNorm_neg]
  exact (matNorm_mul _ _).trans ((mul_le_mul he
    (inverse_bound_of_residual A C b e hc he hb he1) (matNorm_nonneg _) he0).trans_eq (by ring))
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

lemma RI.mem_inv {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo ∨ a.hi < 0) :
    a.inv.Mem x⁻¹ := by
  unfold RI.inv
  split_ifs with hh
  · have hp : 0 < a.neg.lo := by simpa [RI.neg] using neg_pos.mpr hh
    simpa using RI.mem_neg (RI.mem_invPos (RI.mem_neg hx) hp)
  · exact RI.mem_invPos hx (ha.resolve_right hh)

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma jetBox3_1_calc : waveDerivativeBox 3 1 = jetBox3_1 := by decide +kernel
lemma jetBox3_1_mem : jetBox3_1.Mem (waveDerivative 3 ((1:ℤ):ℂ)) := by
  rw [← jetBox3_1_calc]
  exact waveDerivativeBox_mem 3 1
lemma DBox1_calc : jetBox3_1.re.mul ((RI.point 6).mul QBox1).inv = DBox1 := by decide +kernel
lemma DBox1_mem : DBox1.Mem (D 1) := by
  rw [← DBox1_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_1_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox1_mem
  · left; decide +kernel
lemma jetBox3_3_calc : waveDerivativeBox 3 3 = jetBox3_3 := by decide +kernel
lemma jetBox3_3_mem : jetBox3_3.Mem (waveDerivative 3 ((3:ℤ):ℂ)) := by
  rw [← jetBox3_3_calc]
  exact waveDerivativeBox_mem 3 3
lemma DBox3_calc : jetBox3_3.re.mul ((RI.point 6).mul QBox3).inv = DBox3 := by decide +kernel
lemma DBox3_mem : DBox3.Mem (D 3) := by
  rw [← DBox3_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_3_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox3_mem
  · left; decide +kernel
lemma jetBox3_4_calc : waveDerivativeBox 3 4 = jetBox3_4 := by decide +kernel
lemma jetBox3_4_mem : jetBox3_4.Mem (waveDerivative 3 ((4:ℤ):ℂ)) := by
  rw [← jetBox3_4_calc]
  exact waveDerivativeBox_mem 3 4
lemma DBox4_calc : jetBox3_4.re.mul ((RI.point 6).mul QBox4).inv = DBox4 := by decide +kernel
lemma DBox4_mem : DBox4.Mem (D 4) := by
  rw [← DBox4_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_4_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox4_mem
  · left; decide +kernel
lemma jetBox3_7_calc : waveDerivativeBox 3 7 = jetBox3_7 := by decide +kernel
lemma jetBox3_7_mem : jetBox3_7.Mem (waveDerivative 3 ((7:ℤ):ℂ)) := by
  rw [← jetBox3_7_calc]
  exact waveDerivativeBox_mem 3 7
lemma DBox7_calc : jetBox3_7.re.mul ((RI.point 6).mul QBox7).inv = DBox7 := by decide +kernel
lemma DBox7_mem : DBox7.Mem (D 7) := by
  rw [← DBox7_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_7_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox7_mem
  · left; decide +kernel
lemma jetBox3_9_calc : waveDerivativeBox 3 9 = jetBox3_9 := by decide +kernel
lemma jetBox3_9_mem : jetBox3_9.Mem (waveDerivative 3 ((9:ℤ):ℂ)) := by
  rw [← jetBox3_9_calc]
  exact waveDerivativeBox_mem 3 9
lemma DBox9_calc : jetBox3_9.re.mul ((RI.point 6).mul QBox9).inv = DBox9 := by decide +kernel
lemma DBox9_mem : DBox9.Mem (D 9) := by
  rw [← DBox9_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_9_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox9_mem
  · left; decide +kernel
lemma jetBox3_12_calc : waveDerivativeBox 3 12 = jetBox3_12 := by decide +kernel
lemma jetBox3_12_mem : jetBox3_12.Mem (waveDerivative 3 ((12:ℤ):ℂ)) := by
  rw [← jetBox3_12_calc]
  exact waveDerivativeBox_mem 3 12
lemma DBox12_calc : jetBox3_12.re.mul ((RI.point 6).mul QBox12).inv = DBox12 := by decide +kernel
lemma DBox12_mem : DBox12.Mem (D 12) := by
  rw [← DBox12_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_12_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox12_mem
  · left; decide +kernel
lemma jetBox3_13_calc : waveDerivativeBox 3 13 = jetBox3_13 := by decide +kernel
lemma jetBox3_13_mem : jetBox3_13.Mem (waveDerivative 3 ((13:ℤ):ℂ)) := by
  rw [← jetBox3_13_calc]
  exact waveDerivativeBox_mem 3 13
lemma DBox13_calc : jetBox3_13.re.mul ((RI.point 6).mul QBox13).inv = DBox13 := by decide +kernel
lemma DBox13_mem : DBox13.Mem (D 13) := by
  rw [← DBox13_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_13_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox13_mem
  · left; decide +kernel
lemma jetBox3_16_calc : waveDerivativeBox 3 16 = jetBox3_16 := by decide +kernel
lemma jetBox3_16_mem : jetBox3_16.Mem (waveDerivative 3 ((16:ℤ):ℂ)) := by
  rw [← jetBox3_16_calc]
  exact waveDerivativeBox_mem 3 16
lemma DBox16_calc : jetBox3_16.re.mul ((RI.point 6).mul QBox16).inv = DBox16 := by decide +kernel
lemma DBox16_mem : DBox16.Mem (D 16) := by
  rw [← DBox16_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_16_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox16_mem
  · left; decide +kernel
lemma jetBox3_19_calc : waveDerivativeBox 3 19 = jetBox3_19 := by decide +kernel
lemma jetBox3_19_mem : jetBox3_19.Mem (waveDerivative 3 ((19:ℤ):ℂ)) := by
  rw [← jetBox3_19_calc]
  exact waveDerivativeBox_mem 3 19
lemma DBox19_calc : jetBox3_19.re.mul ((RI.point 6).mul QBox19).inv = DBox19 := by decide +kernel
lemma DBox19_mem : DBox19.Mem (D 19) := by
  rw [← DBox19_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_19_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox19_mem
  · left; decide +kernel
lemma jetBox3_21_calc : waveDerivativeBox 3 21 = jetBox3_21 := by decide +kernel
lemma jetBox3_21_mem : jetBox3_21.Mem (waveDerivative 3 ((21:ℤ):ℂ)) := by
  rw [← jetBox3_21_calc]
  exact waveDerivativeBox_mem 3 21
lemma DBox21_calc : jetBox3_21.re.mul ((RI.point 6).mul QBox21).inv = DBox21 := by decide +kernel
lemma DBox21_mem : DBox21.Mem (D 21) := by
  rw [← DBox21_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_21_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox21_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma QTable_mem (a : Fin 10) : (QTable a).Mem (Q (finiteNode a)) := by
  fin_cases a
  · exact QBox1_mem
  · exact QBox3_mem
  · exact QBox4_mem
  · exact QBox7_mem
  · exact QBox9_mem
  · exact QBox12_mem
  · exact QBox13_mem
  · exact QBox16_mem
  · exact QBox19_mem
  · exact QBox21_mem
lemma DTable_mem (a : Fin 10) : (DTable a).Mem (D (finiteNode a)) := by
  fin_cases a
  · exact DBox1_mem
  · exact DBox3_mem
  · exact DBox4_mem
  · exact DBox7_mem
  · exact DBox9_mem
  · exact DBox12_mem
  · exact DBox13_mem
  · exact DBox16_mem
  · exact DBox19_mem
  · exact DBox21_mem

end AtomicTriangular.FiniteCertificate
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
omit [Fintype m] [Fintype p] in
lemma matrixMul_mem {a : m → n → RI} {b : n → p → RI}
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} (ha : ∀ i j, (a i j).Mem (A i j))
    (hb : ∀ i j, (b i j).Mem (B i j)) (i : m) (j : p) :
    (matrixMul a b i j).Mem ((A*B) i j) :=
  RI.mem_sum (fun k => RI.mem_mul (ha i k) (hb k j))
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

lemma matrixEntry_le_norm [Nonempty n] (A : Matrix m n ℝ) (i : m) (j : n) :
    |A i j| ≤ matNorm A := by
  have hh : |A i j| ≤ colNorm A j :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A k j)) (Finset.mem_univ i)
  exact hh.trans (colNorm_le_matNorm A j)
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
lemma minusResidual_bound : matNorm (minusApprox*(1 - Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) minusResidualTable_mem_x (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma minusInverse_error : matNorm ((1 - Construction.R)⁻¹-minusApprox) ≤ (1:ℝ)/10^23 := by
  exact (inverse_error_of_residual _ _ (16155/1000) ((1:ℝ)/10^26)
    minusApprox_bound minusResidual_bound (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)
lemma minusInverseBox_mem (i j : Fin 20) :
    (minusInverseBox i j).Mem (((1 - Construction.R)⁻¹) i j) := by
  apply RI.mem_widen (minusApproxBox_mem i j)
  have hh := (matrixEntry_le_norm ((1 - Construction.R)⁻¹-minusApprox) i j).trans minusInverse_error
  norm_num [scale] at hh ⊢
  exact hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma etaPiBox_mem : etaPiBox.Mem (Real.pi*eta) := by
  apply RI.mem_mul piBox_mem
  simpa [eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<(5:ℕ))
lemma targetExp1_calc : (CI.ofReal (etaPiBox.mul (RI.point 1))).exp = targetExp1 := by decide +kernel
lemma targetExp1_mem : targetExp1.Mem (Complex.exp ((Real.pi*eta*(1:ℤ):ℝ):ℂ)) := by
  rw [← targetExp1_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 1))
  · decide +kernel
lemma targetExp3_calc : (CI.ofReal (etaPiBox.mul (RI.point 3))).exp = targetExp3 := by decide +kernel
lemma targetExp3_mem : targetExp3.Mem (Complex.exp ((Real.pi*eta*(3:ℤ):ℝ):ℂ)) := by
  rw [← targetExp3_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 3))
  · decide +kernel
lemma targetExp4_calc : (CI.ofReal (etaPiBox.mul (RI.point 4))).exp = targetExp4 := by decide +kernel
lemma targetExp4_mem : targetExp4.Mem (Complex.exp ((Real.pi*eta*(4:ℤ):ℝ):ℂ)) := by
  rw [← targetExp4_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 4))
  · decide +kernel
lemma targetExp7_calc : (CI.ofReal (etaPiBox.mul (RI.point 7))).exp = targetExp7 := by decide +kernel
lemma targetExp7_mem : targetExp7.Mem (Complex.exp ((Real.pi*eta*(7:ℤ):ℝ):ℂ)) := by
  rw [← targetExp7_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 7))
  · decide +kernel
lemma targetExp9_calc : (CI.ofReal (etaPiBox.mul (RI.point 9))).exp = targetExp9 := by decide +kernel
lemma targetExp9_mem : targetExp9.Mem (Complex.exp ((Real.pi*eta*(9:ℤ):ℝ):ℂ)) := by
  rw [← targetExp9_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 9))
  · decide +kernel
lemma targetExp12_calc : (CI.ofReal (etaPiBox.mul (RI.point 12))).exp = targetExp12 := by decide +kernel
lemma targetExp12_mem : targetExp12.Mem (Complex.exp ((Real.pi*eta*(12:ℤ):ℝ):ℂ)) := by
  rw [← targetExp12_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 12))
  · decide +kernel
lemma targetExp13_calc : (CI.ofReal (etaPiBox.mul (RI.point 13))).exp = targetExp13 := by decide +kernel
lemma targetExp13_mem : targetExp13.Mem (Complex.exp ((Real.pi*eta*(13:ℤ):ℝ):ℂ)) := by
  rw [← targetExp13_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 13))
  · decide +kernel
lemma targetExp16_calc : (CI.ofReal (etaPiBox.mul (RI.point 16))).exp = targetExp16 := by decide +kernel
lemma targetExp16_mem : targetExp16.Mem (Complex.exp ((Real.pi*eta*(16:ℤ):ℝ):ℂ)) := by
  rw [← targetExp16_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 16))
  · decide +kernel
lemma targetExp19_calc : (CI.ofReal (etaPiBox.mul (RI.point 19))).exp = targetExp19 := by decide +kernel
lemma targetExp19_mem : targetExp19.Mem (Complex.exp ((Real.pi*eta*(19:ℤ):ℝ):ℂ)) := by
  rw [← targetExp19_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 19))
  · decide +kernel
lemma targetExp21_calc : (CI.ofReal (etaPiBox.mul (RI.point 21))).exp = targetExp21 := by decide +kernel
lemma targetExp21_mem : targetExp21.Mem (Complex.exp ((Real.pi*eta*(21:ℤ):ℝ):ℂ)) := by
  rw [← targetExp21_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 21))
  · decide +kernel
lemma targetExpTable_mem (n : Fin 10) : (targetExpTable n).Mem (Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ)) := by
  fin_cases n
  · exact targetExp1_mem
  · exact targetExp3_mem
  · exact targetExp4_mem
  · exact targetExp7_mem
  · exact targetExp9_mem
  · exact targetExp12_mem
  · exact targetExp13_mem
  · exact targetExp16_mem
  · exact targetExp19_mem
  · exact targetExp21_mem
lemma targetCoefficientBox_mem (n : Fin 10) : (targetCoefficientBox n).Mem (targetCoefficient n) := by
  have he : ((Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ))).re = Real.exp (Real.pi*eta*(finiteNode n)) := by rw [Complex.exp_ofReal_re]
  have hq : ∀ n : Fin 10, 0 < (QTable n).lo := by decide +kernel
  unfold targetCoefficient
  rw [div_eq_mul_inv]
  apply RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos (QTable_mem n) (hq n)))
  simpa only [he] using (targetExpTable_mem n).1

lemma YfBox_mem (i : Fin 20) (j : Fin 8) : (YfBox i j).Mem (Yf i j) := by
  unfold YfBox Yf
  split_ifs
  all_goals first
    | apply RI.mem_mul (targetCoefficientBox_mem _); first
        | simpa using RI.mem_point 1
        | simpa using RI.mem_point (-1)
        | simpa using RI.mem_point 0
        | exact RI.mem_sub etaPiBox_mem (DTable_mem _)
    | simpa using RI.mem_point 0

lemma gammaBox_mem (side : Fin 2) (i : Fin 3) (j : Fin 8) : (gammaBox side i j).Mem (gamma side i j) := by
  unfold gammaBox gamma
  split_ifs
  all_goals first
    | simpa using RI.mem_point 0
    | simpa using RI.mem_divNat (RI.mem_point 11) (by norm_num : 0<(25:ℕ))
    | simpa using RI.mem_neg (RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ)))
    | simpa using RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ))

lemma rhsPlusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsPlusBox i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem_x (fun k j => RI.mem_add (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma rhsPlusTableRow0_calc (j : Fin 8) : rhsPlusBox 0 j = rhsPlusTableRow0 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow1_calc (j : Fin 8) : rhsPlusBox 1 j = rhsPlusTableRow1 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow2_calc (j : Fin 8) : rhsPlusBox 2 j = rhsPlusTableRow2 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow3_calc (j : Fin 8) : rhsPlusBox 3 j = rhsPlusTableRow3 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow4_calc (j : Fin 8) : rhsPlusBox 4 j = rhsPlusTableRow4 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow5_calc (j : Fin 8) : rhsPlusBox 5 j = rhsPlusTableRow5 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow6_calc (j : Fin 8) : rhsPlusBox 6 j = rhsPlusTableRow6 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow7_calc (j : Fin 8) : rhsPlusBox 7 j = rhsPlusTableRow7 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow8_calc (j : Fin 8) : rhsPlusBox 8 j = rhsPlusTableRow8 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow9_calc (j : Fin 8) : rhsPlusBox 9 j = rhsPlusTableRow9 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow10_calc (j : Fin 8) : rhsPlusBox 10 j = rhsPlusTableRow10 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow11_calc (j : Fin 8) : rhsPlusBox 11 j = rhsPlusTableRow11 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow12_calc (j : Fin 8) : rhsPlusBox 12 j = rhsPlusTableRow12 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow13_calc (j : Fin 8) : rhsPlusBox 13 j = rhsPlusTableRow13 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow14_calc (j : Fin 8) : rhsPlusBox 14 j = rhsPlusTableRow14 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow15_calc (j : Fin 8) : rhsPlusBox 15 j = rhsPlusTableRow15 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow16_calc (j : Fin 8) : rhsPlusBox 16 j = rhsPlusTableRow16 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow17_calc (j : Fin 8) : rhsPlusBox 17 j = rhsPlusTableRow17 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow18_calc (j : Fin 8) : rhsPlusBox 18 j = rhsPlusTableRow18 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow19_calc (j : Fin 8) : rhsPlusBox 19 j = rhsPlusTableRow19 j := by
  revert j
  decide +kernel
lemma rhsPlusTable_calc (i : Fin 20) (j : Fin 8) : rhsPlusBox i j = rhsPlusTable i j := by
  fin_cases i
  · exact rhsPlusTableRow0_calc j
  · exact rhsPlusTableRow1_calc j
  · exact rhsPlusTableRow2_calc j
  · exact rhsPlusTableRow3_calc j
  · exact rhsPlusTableRow4_calc j
  · exact rhsPlusTableRow5_calc j
  · exact rhsPlusTableRow6_calc j
  · exact rhsPlusTableRow7_calc j
  · exact rhsPlusTableRow8_calc j
  · exact rhsPlusTableRow9_calc j
  · exact rhsPlusTableRow10_calc j
  · exact rhsPlusTableRow11_calc j
  · exact rhsPlusTableRow12_calc j
  · exact rhsPlusTableRow13_calc j
  · exact rhsPlusTableRow14_calc j
  · exact rhsPlusTableRow15_calc j
  · exact rhsPlusTableRow16_calc j
  · exact rhsPlusTableRow17_calc j
  · exact rhsPlusTableRow18_calc j
  · exact rhsPlusTableRow19_calc j
lemma rhsPlusTable_mem (i : Fin 20) (j : Fin 8) : (rhsPlusTable i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) := by
  rw [← rhsPlusTable_calc]
  exact rhsPlusBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma UplusCachedBox_mem_x_oai (i : Fin 20) (j : Fin 8) : (UplusCachedBox i j).Mem (Uplus i j) := matrixMul_mem minusInverseBox_mem rhsPlusTable_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox_mem_x_oai
