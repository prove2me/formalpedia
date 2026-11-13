-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.finiteApprox_norm_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:13:22.030204+00:00
-- url     : https://prove2.me/submissions/b2a14042-45d4-4fc0-a53b-7ae231adc228

import Mathlib
import Definitions.Def_OAIQ334E021
import Definitions.Def_OAIQ334E022
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_R0Box_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UplusTable_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_plusBlockBox_mem_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Auxiliary_MatrixNorm
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
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

lemma RI.mem_min {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imin b).Mem (min x y) := by
  constructor
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.1 hy.1
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.2 hy.2

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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveExpData
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_MatrixInterval
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
omit [Fintype n] in
lemma matrixOne_mem [DecidableEq n] (i j : n) : (matrixOne i j).Mem ((1:Matrix n n ℝ) i j) := by
  simpa only [matrixOne,Matrix.one_apply,Int.cast_ite,Int.cast_zero,Int.cast_one] using
    RI.mem_point (if i=j then 1 else 0)

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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
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
lemma plusResidualBox_mem (i j : Fin 20) :
    (plusResidualBox i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) :=
  RI.mem_sub (matrixMul_mem plusApproxBox_mem plusBlockBox_mem_eu i j) (matrixOne_mem i j)
lemma plusResidualRow0_calc (j : Fin 20) : plusResidualBox 0 j = plusResidualRow0 j := by
  revert j
  decide +kernel
lemma plusResidualRow0_mem (j : Fin 20) :
    (plusResidualRow0 j).Mem ((plusApprox*(1 + Construction.R)-1) 0 j) := by
  rw [← plusResidualRow0_calc]
  exact plusResidualBox_mem 0 j
lemma plusResidualRow1_calc (j : Fin 20) : plusResidualBox 1 j = plusResidualRow1 j := by
  revert j
  decide +kernel
lemma plusResidualRow1_mem (j : Fin 20) :
    (plusResidualRow1 j).Mem ((plusApprox*(1 + Construction.R)-1) 1 j) := by
  rw [← plusResidualRow1_calc]
  exact plusResidualBox_mem 1 j
lemma plusResidualRow2_calc (j : Fin 20) : plusResidualBox 2 j = plusResidualRow2 j := by
  revert j
  decide +kernel
lemma plusResidualRow2_mem (j : Fin 20) :
    (plusResidualRow2 j).Mem ((plusApprox*(1 + Construction.R)-1) 2 j) := by
  rw [← plusResidualRow2_calc]
  exact plusResidualBox_mem 2 j
lemma plusResidualRow3_calc (j : Fin 20) : plusResidualBox 3 j = plusResidualRow3 j := by
  revert j
  decide +kernel
lemma plusResidualRow3_mem (j : Fin 20) :
    (plusResidualRow3 j).Mem ((plusApprox*(1 + Construction.R)-1) 3 j) := by
  rw [← plusResidualRow3_calc]
  exact plusResidualBox_mem 3 j
lemma plusResidualRow4_calc (j : Fin 20) : plusResidualBox 4 j = plusResidualRow4 j := by
  revert j
  decide +kernel
lemma plusResidualRow4_mem (j : Fin 20) :
    (plusResidualRow4 j).Mem ((plusApprox*(1 + Construction.R)-1) 4 j) := by
  rw [← plusResidualRow4_calc]
  exact plusResidualBox_mem 4 j
lemma plusResidualRow5_calc (j : Fin 20) : plusResidualBox 5 j = plusResidualRow5 j := by
  revert j
  decide +kernel
lemma plusResidualRow5_mem (j : Fin 20) :
    (plusResidualRow5 j).Mem ((plusApprox*(1 + Construction.R)-1) 5 j) := by
  rw [← plusResidualRow5_calc]
  exact plusResidualBox_mem 5 j
lemma plusResidualRow6_calc (j : Fin 20) : plusResidualBox 6 j = plusResidualRow6 j := by
  revert j
  decide +kernel
lemma plusResidualRow6_mem (j : Fin 20) :
    (plusResidualRow6 j).Mem ((plusApprox*(1 + Construction.R)-1) 6 j) := by
  rw [← plusResidualRow6_calc]
  exact plusResidualBox_mem 6 j
lemma plusResidualRow7_calc (j : Fin 20) : plusResidualBox 7 j = plusResidualRow7 j := by
  revert j
  decide +kernel
lemma plusResidualRow7_mem (j : Fin 20) :
    (plusResidualRow7 j).Mem ((plusApprox*(1 + Construction.R)-1) 7 j) := by
  rw [← plusResidualRow7_calc]
  exact plusResidualBox_mem 7 j
lemma plusResidualRow8_calc (j : Fin 20) : plusResidualBox 8 j = plusResidualRow8 j := by
  revert j
  decide +kernel
lemma plusResidualRow8_mem (j : Fin 20) :
    (plusResidualRow8 j).Mem ((plusApprox*(1 + Construction.R)-1) 8 j) := by
  rw [← plusResidualRow8_calc]
  exact plusResidualBox_mem 8 j
lemma plusResidualRow9_calc (j : Fin 20) : plusResidualBox 9 j = plusResidualRow9 j := by
  revert j
  decide +kernel
lemma plusResidualRow9_mem (j : Fin 20) :
    (plusResidualRow9 j).Mem ((plusApprox*(1 + Construction.R)-1) 9 j) := by
  rw [← plusResidualRow9_calc]
  exact plusResidualBox_mem 9 j
lemma plusResidualRow10_calc (j : Fin 20) : plusResidualBox 10 j = plusResidualRow10 j := by
  revert j
  decide +kernel
lemma plusResidualRow10_mem (j : Fin 20) :
    (plusResidualRow10 j).Mem ((plusApprox*(1 + Construction.R)-1) 10 j) := by
  rw [← plusResidualRow10_calc]
  exact plusResidualBox_mem 10 j
lemma plusResidualRow11_calc (j : Fin 20) : plusResidualBox 11 j = plusResidualRow11 j := by
  revert j
  decide +kernel
lemma plusResidualRow11_mem (j : Fin 20) :
    (plusResidualRow11 j).Mem ((plusApprox*(1 + Construction.R)-1) 11 j) := by
  rw [← plusResidualRow11_calc]
  exact plusResidualBox_mem 11 j
lemma plusResidualRow12_calc (j : Fin 20) : plusResidualBox 12 j = plusResidualRow12 j := by
  revert j
  decide +kernel
lemma plusResidualRow12_mem (j : Fin 20) :
    (plusResidualRow12 j).Mem ((plusApprox*(1 + Construction.R)-1) 12 j) := by
  rw [← plusResidualRow12_calc]
  exact plusResidualBox_mem 12 j
lemma plusResidualRow13_calc (j : Fin 20) : plusResidualBox 13 j = plusResidualRow13 j := by
  revert j
  decide +kernel
lemma plusResidualRow13_mem (j : Fin 20) :
    (plusResidualRow13 j).Mem ((plusApprox*(1 + Construction.R)-1) 13 j) := by
  rw [← plusResidualRow13_calc]
  exact plusResidualBox_mem 13 j
lemma plusResidualRow14_calc (j : Fin 20) : plusResidualBox 14 j = plusResidualRow14 j := by
  revert j
  decide +kernel
lemma plusResidualRow14_mem (j : Fin 20) :
    (plusResidualRow14 j).Mem ((plusApprox*(1 + Construction.R)-1) 14 j) := by
  rw [← plusResidualRow14_calc]
  exact plusResidualBox_mem 14 j
lemma plusResidualRow15_calc (j : Fin 20) : plusResidualBox 15 j = plusResidualRow15 j := by
  revert j
  decide +kernel
lemma plusResidualRow15_mem (j : Fin 20) :
    (plusResidualRow15 j).Mem ((plusApprox*(1 + Construction.R)-1) 15 j) := by
  rw [← plusResidualRow15_calc]
  exact plusResidualBox_mem 15 j
lemma plusResidualRow16_calc (j : Fin 20) : plusResidualBox 16 j = plusResidualRow16 j := by
  revert j
  decide +kernel
lemma plusResidualRow16_mem (j : Fin 20) :
    (plusResidualRow16 j).Mem ((plusApprox*(1 + Construction.R)-1) 16 j) := by
  rw [← plusResidualRow16_calc]
  exact plusResidualBox_mem 16 j
lemma plusResidualRow17_calc (j : Fin 20) : plusResidualBox 17 j = plusResidualRow17 j := by
  revert j
  decide +kernel
lemma plusResidualRow17_mem (j : Fin 20) :
    (plusResidualRow17 j).Mem ((plusApprox*(1 + Construction.R)-1) 17 j) := by
  rw [← plusResidualRow17_calc]
  exact plusResidualBox_mem 17 j
lemma plusResidualRow18_calc (j : Fin 20) : plusResidualBox 18 j = plusResidualRow18 j := by
  revert j
  decide +kernel
lemma plusResidualRow18_mem (j : Fin 20) :
    (plusResidualRow18 j).Mem ((plusApprox*(1 + Construction.R)-1) 18 j) := by
  rw [← plusResidualRow18_calc]
  exact plusResidualBox_mem 18 j
lemma plusResidualRow19_calc (j : Fin 20) : plusResidualBox 19 j = plusResidualRow19 j := by
  revert j
  decide +kernel
lemma plusResidualRow19_mem (j : Fin 20) :
    (plusResidualRow19 j).Mem ((plusApprox*(1 + Construction.R)-1) 19 j) := by
  rw [← plusResidualRow19_calc]
  exact plusResidualBox_mem 19 j
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
lemma plusInverse_error : matNorm ((1 + Construction.R)⁻¹-plusApprox) ≤ (1:ℝ)/10^23 := by
  exact (inverse_error_of_residual _ _ (3885/1000) ((1:ℝ)/10^26)
    plusApprox_bound plusResidual_bound (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)
lemma plusInverseBox_mem (i j : Fin 20) :
    (plusInverseBox i j).Mem (((1 + Construction.R)⁻¹) i j) := by
  apply RI.mem_widen (plusApproxBox_mem i j)
  have hh := (matrixEntry_le_norm ((1 + Construction.R)⁻¹-plusApprox) i j).trans plusInverse_error
  norm_num [scale] at hh ⊢
  exact hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamInterval
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

lemma rhsMinusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsMinusBox i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem_eu (fun k j => RI.mem_sub (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma rhsMinusTableRow0_calc (j : Fin 8) : rhsMinusBox 0 j = rhsMinusTableRow0 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow1_calc (j : Fin 8) : rhsMinusBox 1 j = rhsMinusTableRow1 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow2_calc (j : Fin 8) : rhsMinusBox 2 j = rhsMinusTableRow2 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow3_calc (j : Fin 8) : rhsMinusBox 3 j = rhsMinusTableRow3 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow4_calc (j : Fin 8) : rhsMinusBox 4 j = rhsMinusTableRow4 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow5_calc (j : Fin 8) : rhsMinusBox 5 j = rhsMinusTableRow5 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow6_calc (j : Fin 8) : rhsMinusBox 6 j = rhsMinusTableRow6 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow7_calc (j : Fin 8) : rhsMinusBox 7 j = rhsMinusTableRow7 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow8_calc (j : Fin 8) : rhsMinusBox 8 j = rhsMinusTableRow8 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow9_calc (j : Fin 8) : rhsMinusBox 9 j = rhsMinusTableRow9 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow10_calc (j : Fin 8) : rhsMinusBox 10 j = rhsMinusTableRow10 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow11_calc (j : Fin 8) : rhsMinusBox 11 j = rhsMinusTableRow11 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow12_calc (j : Fin 8) : rhsMinusBox 12 j = rhsMinusTableRow12 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow13_calc (j : Fin 8) : rhsMinusBox 13 j = rhsMinusTableRow13 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow14_calc (j : Fin 8) : rhsMinusBox 14 j = rhsMinusTableRow14 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow15_calc (j : Fin 8) : rhsMinusBox 15 j = rhsMinusTableRow15 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow16_calc (j : Fin 8) : rhsMinusBox 16 j = rhsMinusTableRow16 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow17_calc (j : Fin 8) : rhsMinusBox 17 j = rhsMinusTableRow17 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow18_calc (j : Fin 8) : rhsMinusBox 18 j = rhsMinusTableRow18 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow19_calc (j : Fin 8) : rhsMinusBox 19 j = rhsMinusTableRow19 j := by
  revert j
  decide +kernel
lemma rhsMinusTable_calc (i : Fin 20) (j : Fin 8) : rhsMinusBox i j = rhsMinusTable i j := by
  fin_cases i
  · exact rhsMinusTableRow0_calc j
  · exact rhsMinusTableRow1_calc j
  · exact rhsMinusTableRow2_calc j
  · exact rhsMinusTableRow3_calc j
  · exact rhsMinusTableRow4_calc j
  · exact rhsMinusTableRow5_calc j
  · exact rhsMinusTableRow6_calc j
  · exact rhsMinusTableRow7_calc j
  · exact rhsMinusTableRow8_calc j
  · exact rhsMinusTableRow9_calc j
  · exact rhsMinusTableRow10_calc j
  · exact rhsMinusTableRow11_calc j
  · exact rhsMinusTableRow12_calc j
  · exact rhsMinusTableRow13_calc j
  · exact rhsMinusTableRow14_calc j
  · exact rhsMinusTableRow15_calc j
  · exact rhsMinusTableRow16_calc j
  · exact rhsMinusTableRow17_calc j
  · exact rhsMinusTableRow18_calc j
  · exact rhsMinusTableRow19_calc j
lemma rhsMinusTable_mem (i : Fin 20) (j : Fin 8) : (rhsMinusTable i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) := by
  rw [← rhsMinusTable_calc]
  exact rhsMinusBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma UminusCachedBox_mem (i : Fin 20) (j : Fin 8) : (UminusCachedBox i j).Mem (Uminus i j) := matrixMul_mem plusInverseBox_mem rhsMinusTable_mem i j
lemma UminusTableRow0_calc (j : Fin 8) : UminusCachedBox 0 j = UminusTableRow0 j := by
  revert j
  decide +kernel
lemma UminusTableRow1_calc (j : Fin 8) : UminusCachedBox 1 j = UminusTableRow1 j := by
  revert j
  decide +kernel
lemma UminusTableRow2_calc (j : Fin 8) : UminusCachedBox 2 j = UminusTableRow2 j := by
  revert j
  decide +kernel
lemma UminusTableRow3_calc (j : Fin 8) : UminusCachedBox 3 j = UminusTableRow3 j := by
  revert j
  decide +kernel
lemma UminusTableRow4_calc (j : Fin 8) : UminusCachedBox 4 j = UminusTableRow4 j := by
  revert j
  decide +kernel
lemma UminusTableRow5_calc (j : Fin 8) : UminusCachedBox 5 j = UminusTableRow5 j := by
  revert j
  decide +kernel
lemma UminusTableRow6_calc (j : Fin 8) : UminusCachedBox 6 j = UminusTableRow6 j := by
  revert j
  decide +kernel
lemma UminusTableRow7_calc (j : Fin 8) : UminusCachedBox 7 j = UminusTableRow7 j := by
  revert j
  decide +kernel
lemma UminusTableRow8_calc (j : Fin 8) : UminusCachedBox 8 j = UminusTableRow8 j := by
  revert j
  decide +kernel
lemma UminusTableRow9_calc (j : Fin 8) : UminusCachedBox 9 j = UminusTableRow9 j := by
  revert j
  decide +kernel
lemma UminusTableRow10_calc (j : Fin 8) : UminusCachedBox 10 j = UminusTableRow10 j := by
  revert j
  decide +kernel
lemma UminusTableRow11_calc (j : Fin 8) : UminusCachedBox 11 j = UminusTableRow11 j := by
  revert j
  decide +kernel
lemma UminusTableRow12_calc (j : Fin 8) : UminusCachedBox 12 j = UminusTableRow12 j := by
  revert j
  decide +kernel
lemma UminusTableRow13_calc (j : Fin 8) : UminusCachedBox 13 j = UminusTableRow13 j := by
  revert j
  decide +kernel
lemma UminusTableRow14_calc (j : Fin 8) : UminusCachedBox 14 j = UminusTableRow14 j := by
  revert j
  decide +kernel
lemma UminusTableRow15_calc (j : Fin 8) : UminusCachedBox 15 j = UminusTableRow15 j := by
  revert j
  decide +kernel
lemma UminusTableRow16_calc (j : Fin 8) : UminusCachedBox 16 j = UminusTableRow16 j := by
  revert j
  decide +kernel
lemma UminusTableRow17_calc (j : Fin 8) : UminusCachedBox 17 j = UminusTableRow17 j := by
  revert j
  decide +kernel
lemma UminusTableRow18_calc (j : Fin 8) : UminusCachedBox 18 j = UminusTableRow18 j := by
  revert j
  decide +kernel
lemma UminusTableRow19_calc (j : Fin 8) : UminusCachedBox 19 j = UminusTableRow19 j := by
  revert j
  decide +kernel
lemma UminusTable_calc (i : Fin 20) (j : Fin 8) : UminusCachedBox i j = UminusTable i j := by
  fin_cases i
  · exact UminusTableRow0_calc j
  · exact UminusTableRow1_calc j
  · exact UminusTableRow2_calc j
  · exact UminusTableRow3_calc j
  · exact UminusTableRow4_calc j
  · exact UminusTableRow5_calc j
  · exact UminusTableRow6_calc j
  · exact UminusTableRow7_calc j
  · exact UminusTableRow8_calc j
  · exact UminusTableRow9_calc j
  · exact UminusTableRow10_calc j
  · exact UminusTableRow11_calc j
  · exact UminusTableRow12_calc j
  · exact UminusTableRow13_calc j
  · exact UminusTableRow14_calc j
  · exact UminusTableRow15_calc j
  · exact UminusTableRow16_calc j
  · exact UminusTableRow17_calc j
  · exact UminusTableRow18_calc j
  · exact UminusTableRow19_calc j
lemma UminusTable_mem (i : Fin 20) (j : Fin 8) : (UminusTable i j).Mem (Uminus i j) := by
  rw [← UminusTable_calc]
  exact UminusCachedBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma A1CachedBox_mem (i : Fin 23) (j : Fin 8) : (A1CachedBox i j).Mem (Acoefficient 0 i j) := by
  unfold A1CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_add (UplusTable_mem_eu ⟨i.val-2,by omega⟩ j) (UminusTable_mem ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A1TableRow0_calc (j : Fin 8) : A1CachedBox 0 j = A1TableRow0 j := by
  revert j
  decide +kernel
lemma A1TableRow1_calc (j : Fin 8) : A1CachedBox 1 j = A1TableRow1 j := by
  revert j
  decide +kernel
lemma A1TableRow2_calc (j : Fin 8) : A1CachedBox 2 j = A1TableRow2 j := by
  revert j
  decide +kernel
lemma A1TableRow3_calc (j : Fin 8) : A1CachedBox 3 j = A1TableRow3 j := by
  revert j
  decide +kernel
lemma A1TableRow4_calc (j : Fin 8) : A1CachedBox 4 j = A1TableRow4 j := by
  revert j
  decide +kernel
lemma A1TableRow5_calc (j : Fin 8) : A1CachedBox 5 j = A1TableRow5 j := by
  revert j
  decide +kernel
lemma A1TableRow6_calc (j : Fin 8) : A1CachedBox 6 j = A1TableRow6 j := by
  revert j
  decide +kernel
lemma A1TableRow7_calc (j : Fin 8) : A1CachedBox 7 j = A1TableRow7 j := by
  revert j
  decide +kernel
lemma A1TableRow8_calc (j : Fin 8) : A1CachedBox 8 j = A1TableRow8 j := by
  revert j
  decide +kernel
lemma A1TableRow9_calc (j : Fin 8) : A1CachedBox 9 j = A1TableRow9 j := by
  revert j
  decide +kernel
lemma A1TableRow10_calc (j : Fin 8) : A1CachedBox 10 j = A1TableRow10 j := by
  revert j
  decide +kernel
lemma A1TableRow11_calc (j : Fin 8) : A1CachedBox 11 j = A1TableRow11 j := by
  revert j
  decide +kernel
lemma A1TableRow12_calc (j : Fin 8) : A1CachedBox 12 j = A1TableRow12 j := by
  revert j
  decide +kernel
lemma A1TableRow13_calc (j : Fin 8) : A1CachedBox 13 j = A1TableRow13 j := by
  revert j
  decide +kernel
lemma A1TableRow14_calc (j : Fin 8) : A1CachedBox 14 j = A1TableRow14 j := by
  revert j
  decide +kernel
lemma A1TableRow15_calc (j : Fin 8) : A1CachedBox 15 j = A1TableRow15 j := by
  revert j
  decide +kernel
lemma A1TableRow16_calc (j : Fin 8) : A1CachedBox 16 j = A1TableRow16 j := by
  revert j
  decide +kernel
lemma A1TableRow17_calc (j : Fin 8) : A1CachedBox 17 j = A1TableRow17 j := by
  revert j
  decide +kernel
lemma A1TableRow18_calc (j : Fin 8) : A1CachedBox 18 j = A1TableRow18 j := by
  revert j
  decide +kernel
lemma A1TableRow19_calc (j : Fin 8) : A1CachedBox 19 j = A1TableRow19 j := by
  revert j
  decide +kernel
lemma A1TableRow20_calc (j : Fin 8) : A1CachedBox 20 j = A1TableRow20 j := by
  revert j
  decide +kernel
lemma A1TableRow21_calc (j : Fin 8) : A1CachedBox 21 j = A1TableRow21 j := by
  revert j
  decide +kernel
lemma A1TableRow22_calc (j : Fin 8) : A1CachedBox 22 j = A1TableRow22 j := by
  revert j
  decide +kernel
lemma A1Table_calc (i : Fin 23) (j : Fin 8) : A1CachedBox i j = A1Table i j := by
  fin_cases i
  · exact A1TableRow0_calc j
  · exact A1TableRow1_calc j
  · exact A1TableRow2_calc j
  · exact A1TableRow3_calc j
  · exact A1TableRow4_calc j
  · exact A1TableRow5_calc j
  · exact A1TableRow6_calc j
  · exact A1TableRow7_calc j
  · exact A1TableRow8_calc j
  · exact A1TableRow9_calc j
  · exact A1TableRow10_calc j
  · exact A1TableRow11_calc j
  · exact A1TableRow12_calc j
  · exact A1TableRow13_calc j
  · exact A1TableRow14_calc j
  · exact A1TableRow15_calc j
  · exact A1TableRow16_calc j
  · exact A1TableRow17_calc j
  · exact A1TableRow18_calc j
  · exact A1TableRow19_calc j
  · exact A1TableRow20_calc j
  · exact A1TableRow21_calc j
  · exact A1TableRow22_calc j
lemma A1Table_mem (i : Fin 23) (j : Fin 8) : (A1Table i j).Mem ((Acoefficient 0) i j) := by
  rw [← A1Table_calc]
  exact A1CachedBox_mem i j
lemma A2CachedBox_mem (i : Fin 23) (j : Fin 8) : (A2CachedBox i j).Mem (Acoefficient 1 i j) := by
  unfold A2CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_sub (UplusTable_mem_eu ⟨i.val-2,by omega⟩ j) (UminusTable_mem ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A2TableRow0_calc (j : Fin 8) : A2CachedBox 0 j = A2TableRow0 j := by
  revert j
  decide +kernel
lemma A2TableRow1_calc (j : Fin 8) : A2CachedBox 1 j = A2TableRow1 j := by
  revert j
  decide +kernel
lemma A2TableRow2_calc (j : Fin 8) : A2CachedBox 2 j = A2TableRow2 j := by
  revert j
  decide +kernel
lemma A2TableRow3_calc (j : Fin 8) : A2CachedBox 3 j = A2TableRow3 j := by
  revert j
  decide +kernel
lemma A2TableRow4_calc (j : Fin 8) : A2CachedBox 4 j = A2TableRow4 j := by
  revert j
  decide +kernel
lemma A2TableRow5_calc (j : Fin 8) : A2CachedBox 5 j = A2TableRow5 j := by
  revert j
  decide +kernel
lemma A2TableRow6_calc (j : Fin 8) : A2CachedBox 6 j = A2TableRow6 j := by
  revert j
  decide +kernel
lemma A2TableRow7_calc (j : Fin 8) : A2CachedBox 7 j = A2TableRow7 j := by
  revert j
  decide +kernel
lemma A2TableRow8_calc (j : Fin 8) : A2CachedBox 8 j = A2TableRow8 j := by
  revert j
  decide +kernel
lemma A2TableRow9_calc (j : Fin 8) : A2CachedBox 9 j = A2TableRow9 j := by
  revert j
  decide +kernel
lemma A2TableRow10_calc (j : Fin 8) : A2CachedBox 10 j = A2TableRow10 j := by
  revert j
  decide +kernel
lemma A2TableRow11_calc (j : Fin 8) : A2CachedBox 11 j = A2TableRow11 j := by
  revert j
  decide +kernel
lemma A2TableRow12_calc (j : Fin 8) : A2CachedBox 12 j = A2TableRow12 j := by
  revert j
  decide +kernel
lemma A2TableRow13_calc (j : Fin 8) : A2CachedBox 13 j = A2TableRow13 j := by
  revert j
  decide +kernel
lemma A2TableRow14_calc (j : Fin 8) : A2CachedBox 14 j = A2TableRow14 j := by
  revert j
  decide +kernel
lemma A2TableRow15_calc (j : Fin 8) : A2CachedBox 15 j = A2TableRow15 j := by
  revert j
  decide +kernel
lemma A2TableRow16_calc (j : Fin 8) : A2CachedBox 16 j = A2TableRow16 j := by
  revert j
  decide +kernel
lemma A2TableRow17_calc (j : Fin 8) : A2CachedBox 17 j = A2TableRow17 j := by
  revert j
  decide +kernel
lemma A2TableRow18_calc (j : Fin 8) : A2CachedBox 18 j = A2TableRow18 j := by
  revert j
  decide +kernel
lemma A2TableRow19_calc (j : Fin 8) : A2CachedBox 19 j = A2TableRow19 j := by
  revert j
  decide +kernel
lemma A2TableRow20_calc (j : Fin 8) : A2CachedBox 20 j = A2TableRow20 j := by
  revert j
  decide +kernel
lemma A2TableRow21_calc (j : Fin 8) : A2CachedBox 21 j = A2TableRow21 j := by
  revert j
  decide +kernel
lemma A2TableRow22_calc (j : Fin 8) : A2CachedBox 22 j = A2TableRow22 j := by
  revert j
  decide +kernel
lemma A2Table_calc (i : Fin 23) (j : Fin 8) : A2CachedBox i j = A2Table i j := by
  fin_cases i
  · exact A2TableRow0_calc j
  · exact A2TableRow1_calc j
  · exact A2TableRow2_calc j
  · exact A2TableRow3_calc j
  · exact A2TableRow4_calc j
  · exact A2TableRow5_calc j
  · exact A2TableRow6_calc j
  · exact A2TableRow7_calc j
  · exact A2TableRow8_calc j
  · exact A2TableRow9_calc j
  · exact A2TableRow10_calc j
  · exact A2TableRow11_calc j
  · exact A2TableRow12_calc j
  · exact A2TableRow13_calc j
  · exact A2TableRow14_calc j
  · exact A2TableRow15_calc j
  · exact A2TableRow16_calc j
  · exact A2TableRow17_calc j
  · exact A2TableRow18_calc j
  · exact A2TableRow19_calc j
  · exact A2TableRow20_calc j
  · exact A2TableRow21_calc j
  · exact A2TableRow22_calc j
lemma A2Table_mem (i : Fin 23) (j : Fin 8) : (A2Table i j).Mem ((Acoefficient 1) i j) := by
  rw [← A2Table_calc]
  exact A2CachedBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_Polytope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma box_linear_lower {B x c : ℝ} (_hB : 0 ≤ B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    B * min 0 c ≤ c*x := by
  by_cases hc : 0 ≤ c
  · rw [min_eq_left hc]
    simpa using mul_nonneg hc hx
  · rw [min_eq_right (le_of_not_ge hc)]
    nlinarith

lemma triangle_linear_lower {B Z u a v c : ℝ} (_hB : 0 ≤ B) (hu : 0 ≤ u)
    (huB : u ≤ B) (ha : 0 ≤ a) (haZ : a ≤ Z*u) :
    B * min 0 (min v (v+Z*c)) ≤ v*u+c*a := by
  let q := min 0 (min v (v+Z*c))
  have hq0 : q ≤ 0 := min_le_left _ _
  have hqv : q ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hqc : q ≤ v+Z*c := (min_le_right _ _).trans (min_le_right _ _)
  have hqu : B*q ≤ u*q := mul_le_mul_of_nonpos_right huB hq0
  change B*q ≤ _
  by_cases hc : 0 ≤ c
  · have h1 := mul_le_mul_of_nonneg_right hqv hu
    have h2 := mul_nonneg hc ha
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hqc hu
    have h2 := mul_le_mul_of_nonpos_left haZ (le_of_not_ge hc)
    nlinarith

lemma rowLower_le (row e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    rowLower row ≤ ∑ j : Fin 8, row j*e j := by
  rcases he with ⟨z,w,d,u,a,r,p,hz,hzB,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,rfl⟩
  have h1 := box_linear_lower (by norm_num [Z] : 0 ≤ Z) hz hzB (c := row 0)
  have h2 := box_linear_lower (by norm_num [DeltaStar] : 0 ≤ DeltaStar) hd hdB (c := -row 2)
  have h3 := box_linear_lower (by norm_num [Wstar] : 0 ≤ Wstar) hw hwB (c := row 3+Z*row 2)
  have h4 := triangle_linear_lower (by norm_num [Ustar] : 0 ≤ Ustar) hu huB ha haB (v := row 5) (c := row 4)
  have h5 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hr hrB (c := row 6)
  have h6 := box_linear_lower (by norm_num [Pstar] : 0 ≤ Pstar) hp hpB (c := row 7)
  norm_num [Fin.sum_univ_succ, Fin.succ]
  change rowLower row ≤ row 0*z + (row 1 + (row 2*(Z*w-d) + (row 3*w + (row 4*a + (row 5*u + (row 6*r + row 7*p))))))
  unfold rowLower
  nlinarith [h1,h2,h3,h4,h5,h6]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
lemma WstarBox_mem : WstarBox.Mem Wstar := RI.mem_divNat (RI.mem_point 61) (by norm_num)
lemma DeltaStarBox_mem : DeltaStarBox.Mem DeltaStar := RI.mem_divNat (RI.mem_point 18) (by norm_num)
lemma UstarBox_mem : UstarBox.Mem Ustar := RI.mem_divNat (RI.mem_point 48) (by norm_num)
lemma PstarBox_mem : PstarBox.Mem Pstar := RI.mem_divNat (RI.mem_point 3) (by norm_num)
lemma rowLowerBox_mem {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ i, (a i).Mem (v i)) : (rowLowerBox a).Mem (rowLower v) := by
  have hz : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
  unfold rowLowerBox rowLower
  apply RI.mem_add
  · apply RI.mem_add
    · apply RI.mem_add
      · apply RI.mem_add
        · exact RI.mem_add (hv 1) (RI.mem_mul ZBox_mem (RI.mem_min hz (hv 0)))
        · exact RI.mem_mul DeltaStarBox_mem (RI.mem_min hz (RI.mem_neg (hv 2)))
      · exact RI.mem_mul WstarBox_mem (RI.mem_min hz (RI.mem_add (hv 3) (RI.mem_mul ZBox_mem (hv 2))))
    · exact RI.mem_mul UstarBox_mem (RI.mem_min hz (RI.mem_min (hv 5) (RI.mem_add (hv 5) (RI.mem_mul ZBox_mem (hv 4)))))
  · exact RI.mem_mul PstarBox_mem (RI.mem_add (RI.mem_min hz (hv 6)) (RI.mem_min hz (hv 7)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamNormBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma rowAbs_bound {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ j, (a j).Mem (v j)) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    |∑ j : Fin 8, v j*e j| ≤ (rowAbsNumerator a : ℝ)/scale := by
  have h1 := (rowLowerBox_mem hv).1
  have h2 := (rowLowerBox_mem (fun j => RI.mem_neg (hv j))).1
  have h3 := rowLower_le v e he
  have h4 := rowLower_le (fun j => -v j) e he
  have heq : (∑ j : Fin 8, -v j*e j) = -(∑ j : Fin 8, v j*e j) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [heq] at h4
  have hb1 : (-(rowLowerBox a).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_left (-(rowLowerBox a).lo) _)
  have hb2 : (-(rowLowerBox (fun j => (a j).neg)).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_right (-(rowLowerBox a).lo) _)
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h3 scale_pos.le
    nlinarith
  · apply (le_div_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h4 scale_pos.le
    nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma A1AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A1Table i) = A1AbsNumerators i := by
  revert i
  decide +kernel
lemma A1_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j|) < (258/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j| ≤ (A1AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A1AbsNumerators_calc]
    exact rowAbs_bound (A1Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A1AbsNumerators i) < 258*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A1AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (258/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ) < 258*(scale:ℝ) := by exact_mod_cast hc
      linarith
lemma A2AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A2Table i) = A2AbsNumerators i := by
  revert i
  decide +kernel
lemma A2_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j|) < (280/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j| ≤ (A2AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A2AbsNumerators_calc]
    exact rowAbs_bound (A2Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A2AbsNumerators i) < 280*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A2AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (280/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ) < 280*(scale:ℝ) := by exact_mod_cast hc
      linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_ActualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma finiteApprox_norm_eu_oai (side : Fin 2) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    ‖finiteApprox side e‖ < 3 := by
  rw [l1_norm,tsum_fintype]
  have hb : (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) ≤
      ∑ i : Fin 23, |∑ j : Fin 8, Acoefficient side i j*e j| := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  change (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) < 3
  refine hb.trans_lt ?_
  fin_cases side
  · exact (A1_norm_bound e he).trans (by norm_num)
  · exact (A2_norm_bound e he).trans (by norm_num)

end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.finiteApprox_norm_eu_oai := @OAI.AtomicTriangular.Construction.finiteApprox_norm_eu_oai
