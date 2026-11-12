-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.correctionTail_small_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:12.511544+00:00
-- url     : https://prove2.me/submissions/16d632a3-8a41-4fc3-95a8-a36d8726ff9d

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_Bkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Ckernel_summable_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_bound_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_summable_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusInverse_bound_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_plusResidualTable_mem_x

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
lemma plusResidual_bound : matNorm (plusApprox*(1 + Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) plusResidualTable_mem_x (by
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
  ((l1Matrix_norm _).trans_lt FiniteCertificate.minusInverse_bound_x).le.trans (by norm_num)
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

omit [CompleteSpace F] in
lemma neumann_norm (T : F →L[ℝ] F) {q : ℝ} (hq0 : 0≤q) (hq : q<1)
    (hT : ‖T‖≤q) : ‖neumann T‖ ≤ 1/(1-q) := by
  have hs := summable_geometric_of_lt_one hq0 hq
  have hb (n : ℕ) : ‖T^n‖ ≤ q^n := by
    cases n with
    | zero =>
      rw [pow_zero,pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n =>
      exact (norm_pow_le' T (Nat.succ_pos n)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hT (n+1))
  have ht : Summable (fun n : ℕ => ‖T^n‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    ‖neumann T‖ ≤ ∑' n : ℕ, ‖T^n‖ := norm_tsum_le_tsum_norm ht
    _ ≤ ∑' n : ℕ, q^n := ht.tsum_le_tsum hb hs
    _ = 1/(1-q) := by rw [tsum_geometric_of_lt_one hq0 hq,one_div]

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
lemma splitQ_nonneg (e : Fin 2) : 0 ≤ splitQ e := by fin_cases e <;> (first | (simp [splitQ,splitN,beta,delta]; all_goals first | (norm_num [splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [splitQ,splitN,beta,delta]; done) | norm_num [splitQ,splitN,beta,delta])
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

lemma correctionTail_norm (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    ‖correctionTail e r s‖ ≤ (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) := by
  have hn := neumann_norm (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))
    (splitQ_nonneg e) (splitQ_lt e) (splitOperator_norm e)
  have hq : 0≤1/(1-splitQ e) := by exact div_nonneg (by norm_num) (sub_pos.mpr (splitQ_lt e)).le
  have hbeta : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖neumann (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))‖*
        ‖s+splitK e (splitL e r)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1/(1-splitQ e))*(‖s‖+‖splitK e‖*(‖splitL e‖*‖r‖)) := by
      apply mul_le_mul hn _ (norm_nonneg _) hq
      exact (norm_add_le _ _).trans (add_le_add_right ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) _)
    _ ≤ (1/(1-splitQ e))*(‖s‖+beta*(splitN e*‖r‖)) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
    _ = _ := by ring
lemma correctionTail_small_x_oai (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionTail e r s‖ ≤ tailErrorBound e := by
  have hh := correctionTail_norm e r s
  have hb : (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) ≤
      (tailResidualBound e+beta*splitN e*finiteResidualBound)/(1-splitQ e) := by
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr (splitQ_lt e)).le
    apply add_le_add hs
    exact mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num [beta]) (splitN_nonneg e))
  refine (hh.trans hb).trans ?_
  fin_cases e <;> (first | (simp [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; all_goals first | (norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; done) | norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta])
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.correctionTail_small_x_oai := @OAI.AtomicTriangular.Construction.correctionTail_small_x_oai
