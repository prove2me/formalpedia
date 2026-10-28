-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.LocalOrdinaryInput.started_source_control_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:14:08.384786+00:00
-- url     : https://prove2.me/submissions/1f3abdc4-64ae-4757-a40d-081cf7ffc2e0

import Mathlib
import Definitions.Def_OAIQ072A002

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_Spin
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_sum {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (f : α → Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => ∑ a, f a y) x = ∑ a, halfDiff i (f a) x := by
  simp only [halfDiff, sub_div, Finset.sum_sub_distrib, Finset.sum_div]

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_SquaredGaussianFourth
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff.RandomMatrix

lemma matrix_opNorm_sq_le_frobenius {n : ℕ} (A : Interaction n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 ≤ ∑ i, ∑ j, A i j^2 := by
  let S := ∑ i, ∑ j, A i j^2
  have hS : 0 ≤ S := by unfold S; positivity
  have hN : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt S * ‖x‖)).mp
    rw [mul_pow, Real.sq_sqrt hS]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (∑ j, A i j*x j)^2 ≤ S * ∑ j, x j^2
    calc
      _ ≤ ∑ i, (∑ j, A i j^2)*(∑ j, x j^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x)
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hS)

end SKGapCutoff.RandomMatrix

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ScalarVariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma abs_spin_eq_one {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hi : x i <;> simp [spin, hi]

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Taylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGap.SourceTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_taylor (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {L : ℝ}
    (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))-F' x‖≤L*‖t • (y-x)‖) :
    |F y-F x-F' x (y-x)|≤L*‖y-x‖^2 := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))-F x-t*(F' x (y-x))
  let g' : ℝ→ℝ:=fun t=>(F' (x+t • (y-x))-F' x) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have H:=(((hF t ht).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (y-x)).const_add x)).sub_const (F x)).sub
      ((hasDerivAt_id t).mul_const (F' x (y-x)))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',sub_apply,one_smul,one_mul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤L*‖y-x‖^2 := by
    calc
      _ ≤ ‖F' (x+t • (y-x))-F' x‖*‖y-x‖ := (F' (x+t • (y-x))-F' x).le_opNorm _
      _ ≤ (L*‖t • (y-x)‖)*‖y-x‖ := mul_le_mul_of_nonneg_right (hLip t ⟨ht.1,ht.2.le⟩) (norm_nonneg _)
      _ ≤ (L*‖y-x‖)*‖y-x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      _ = _ := by ring
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,one_mul,zero_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using H

lemma segment_lipschitz (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {C : ℝ}
    (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))‖≤C) :
    |F y-F x|≤C*‖y-x‖ := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))
  let g' : ℝ→ℝ:=fun t=>F' (x+t • (y-x)) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    convert! (hF t ht).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',one_smul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤C*‖y-x‖ :=
    ((F' (x+t • (y-x))).le_opNorm _).trans
      (mul_le_mul (hBound t ⟨ht.1,ht.2.le⟩) le_rfl (norm_nonneg _) hC)
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,Real.norm_eq_abs] using H

end SKGap.SourceTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_CoefficientFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGapCutoff.Recipe
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma flipHalfDiff_norm (i : Fin n) (P : Spin n→E) (x : Spin n) :
    ‖flipHalfDiff i P x‖=‖P (flip x i)-P x‖/2 := by
  simp only [flipHalfDiff,norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [norm_sub_rev]
  ring

lemma coefficient_linearization (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (T : E→L[ℝ]ℝ) :
    halfDiff i (fun y=>F (P y)) x-T (flipHalfDiff i P x)=
      (-spin x i/2)*(F (P (flip x i))-F (P x)-T (P (flip x i)-P x)) := by
  rw [halfDiff_as_flip]
  simp only [flipHalfDiff,map_smul,map_sub,smul_eq_mul]
  ring

lemma coefficient_taylor (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {L : ℝ} (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,
      ‖F' (P x+t • (P (flip x i)-P x))-F' (P x)‖≤L*‖t • (P (flip x i)-P x)‖) :
    |halfDiff i (fun y=>F (P y)) x-F' (P x) (flipHalfDiff i P x)|≤
      2*L*‖flipHalfDiff i P x‖^2 := by
  have H:=SKGap.SourceTaylor.segment_taylor F F' (P x) (P (flip x i)) hL hF hLip
  rw [coefficient_linearization,abs_mul,abs_div,abs_neg,abs_spin_eq_one,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm]
  calc
    _ ≤ (1/2:ℝ)*(L*‖P (flip x i)-P x‖^2) := mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring

lemma coefficient_lipschitz (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (P x+t • (P (flip x i)-P x))‖≤C) :
    |halfDiff i (fun y=>F (P y)) x|≤C*‖flipHalfDiff i P x‖ := by
  have H:=SKGap.SourceTaylor.segment_lipschitz F F' (P x) (P (flip x i)) hC hF hBound
  rw [halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right H (show (0:ℝ)≤2 by norm_num)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_FrobeniusSq
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_MatrixSeminorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

omit [DecidableEq ι] in
lemma diagonalSeminorm_sq (M : Matrix ι ι ℝ) : diagonalSeminorm M^2=∑ i,(M i i)^2 := by
  simp only [diagonalSeminorm,EuclideanSpace.norm_sq_eq,diagonalVector,Real.norm_eq_abs,sq_abs]

lemma offDiagonalSeminorm_fourth (M : Matrix ι ι ℝ) :
    offDiagonalSeminorm M^4=∑ p : ι×ι,if p.1=p.2 then 0 else (M p.1 p.2)^4 := by
  rw [offDiagonalSeminorm,PiLp.norm_eq_of_nat (p:=4) 4 (by norm_num)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (Finset.sum_nonneg (fun _ _=>pow_nonneg (norm_nonneg _) _))]
  norm_num only [Nat.cast_ofNat,one_div,mul_inv_cancel₀ (by norm_num : (4:ℝ)≠0),Real.rpow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp only [offDiagonalVector,WithLp.ofLp_toLp]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs]
    calc
      |M p.1 p.2|^4=(|M p.1 p.2|^2)^2 := by ring
      _ = ((M p.1 p.2)^2)^2 := by rw [sq_abs]
      _ = (M p.1 p.2)^4 := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_DiscreteMatrixCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_le_frobenius (M : Interaction n) : SKGap.opNorm M ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [SKGap.frobenius_sq,opNorm_eq]
  exact RandomMatrix.matrix_opNorm_sq_le_frobenius M

lemma fourth_sum (M : Interaction n) :
    (∑ i,∑ k,(M i k)^4) = (∑ i,(M i i)^4)+SKGap.offDiagonalSeminorm M^4 := by
  rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (M i i)^4 = ∑ k : Fin n, if i=k then (M i k)^4 else 0 := by simp
  rw [hs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i=k <;> simp [h]

lemma fourth_sum_le {M : Interaction n} {C : ℝ} (hC : 0≤C) (hM : ShapeBound M C) :
    (∑ i,∑ k,(M i k)^4) ≤ 2*C^4 := by
  rw [fourth_sum]
  have hd : (∑ i,(M i i)^4) ≤ SKGap.diagonalSeminorm M^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,SKGap.diagonalSeminorm_sq]
    simpa only [pow_mul] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (f:=fun i => (M i i)^2)
        (fun i _ => sq_nonneg _))
  have hdC := (pow_le_pow_iff_left₀ (norm_nonneg (SKGap.diagonalVector M)) hC
    (by decide : 4 ≠ 0)).2 hM.2.1
  have hoC := pow_le_pow_left₀ (norm_nonneg (SKGap.offDiagonalVector M)) hM.2.2 4
  dsimp only [SKGap.diagonalSeminorm,SKGap.offDiagonalSeminorm] at hd ⊢
  nlinarith

lemma siteMean_derivative (F : VectorFields n) (x : Spin n) :
    derivativeVector (siteMean F) x = (n:ℝ)⁻¹ •
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
        (WithLp.toLp 2 (fun _ => 1)) := by
  ext k
  change halfDiff k (siteMean F) x = (n:ℝ)⁻¹*(∑ i,halfDiff k (fun y => F y i) x*1)
  simp only [mul_one,halfDiff,siteMean]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma euclidean_ones_norm_sq :
    ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖^2 = n := by
  simp [EuclideanSpace.real_norm_sq_eq]

lemma siteMean_derivative_square (F : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ SKGap.opNorm (derivativeMatrix F x)^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ)).le_opNorm
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))
  change ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))‖ ≤
    SKGap.opNorm ((derivativeMatrix F x)ᵀ) * ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖ at h
  rw [SKGap.opNorm_transpose] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow,euclidean_ones_norm_sq] at hs
  rw [siteMean_derivative,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnR,mul_pow]
  field_simp
  nlinarith

lemma siteMean_derivative_square_bound {F : VectorFields n} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : SKGap.opNorm (derivativeMatrix F x)≤B) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ B^2 :=
  (siteMean_derivative_square F x hn).trans
    (pow_le_pow_left₀ (norm_nonneg _) hB 2)

lemma derivative_norm_of_mean_square {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : 0≤B) (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeVector f x‖≤B := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  nlinarith [sq_nonneg ‖derivativeVector f x‖,norm_nonneg (derivativeVector f x)]

lemma outer_frobenius_bound {v : Fin n→ℝ} {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hv : ∀ i,|v i|≤1) (hB : 0≤B)
    (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖Matrix.of (fun i k => v i*halfDiff k f x)‖≤B := by
  apply nonneg_le_nonneg_of_sq_le_sq hB
  simp only [← sq]
  rw [SKGap.frobenius_sq]
  calc
    _ ≤ ∑ _i : Fin n,∑ k,(halfDiff k f x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      have hi := pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
      simp only [sq_abs,one_pow] at hi
      change (v i*halfDiff k f x)^2 ≤ _
      rw [mul_pow]
      nlinarith [sq_nonneg (halfDiff k f x)]
    _ = (n:ℝ)*‖derivativeVector f x‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        EuclideanSpace.real_norm_sq_eq,derivativeVector]
    _ ≤ B^2 := h

lemma spin_diagonal_frobenius (f : Spin n→ℝ) (x : Spin n) :
    ‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖ = ‖derivativeVector f x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.frobenius_sq,EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.diagonal_apply,derivativeVector,mul_pow,spin_sq]

lemma derivativeMatrix_product (f : Spin n→ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => f y*F y i) x = f x • derivativeMatrix F x +
      Matrix.of (fun i k => F x i*halfDiff k f x) -
      (2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x)) := by
  ext i k
  simp only [derivativeMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.mul_diagonal,halfDiff_mul,Matrix.of_apply]
  ring

lemma product_derivative_error {f : Spin n→ℝ} {F : VectorFields n} {x : Spin n} {B C : ℝ}
    (hn : 0<n) (hB : 0≤B) (hC : SKGap.opNorm (derivativeMatrix F x)≤C)
    (hF : ∀ i,|F x i|≤1) (hf : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeMatrix (fun y i => f y*F y i) x-f x • derivativeMatrix F x‖ ≤ B+2*C*B := by
  have hdb := derivative_norm_of_mean_square hn hB hf
  have hC0 : 0≤C := (norm_nonneg _).trans hC
  rw [derivativeMatrix_product]
  have he (A R T : Interaction n) : A+R-T-A=R-T := by abel
  rw [he]
  calc
    _ ≤ ‖Matrix.of (fun i k => F x i*halfDiff k f x)‖+
        ‖(2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x))‖ := norm_sub_le _ _
    _ ≤ B+2*C*B := by
      apply add_le_add (outer_frobenius_bound hF hB hf)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        _ ≤ 2*(SKGap.opNorm (derivativeMatrix F x)*‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖) :=
          mul_le_mul_of_nonneg_left (SKGap.frobenius_mul_le_opNorm _ _) (by norm_num)
        _ ≤ 2*(C*B) := by
          rw [spin_diagonal_frobenius]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hC hdb (norm_nonneg _) hC0) (by norm_num)
        _ = _ := by ring

lemma derivativeMatrix_linear (J : Interaction n) (F : VectorFields n) (h : Fin n→ℝ)
    (x : Spin n) :
    derivativeMatrix (fun y i => h i+∑ k,J i k*F y k) x = J*derivativeMatrix F x := by
  ext i l
  simp only [derivativeMatrix,Matrix.mul_apply,halfDiff]
  simp_rw [← mul_div_assoc,mul_sub]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma derivativeMatrix_smul (c : ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => c*F y i) x=c • derivativeMatrix F x := by
  ext i k
  simp only [derivativeMatrix,halfDiff,Matrix.smul_apply,smul_eq_mul]
  ring

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_LocalCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma linear_apply_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (T : (α→ℝ)→L[ℝ]ℝ) (v : α→ℝ) : T v=∑l,v l*T (Pi.single l 1) := by
  have he : v=∑l,v l • Pi.single l (1:ℝ) := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

lemma coefficient_chain (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n)
    (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) :
    T (flipHalfDiff k (fun y=>localArgs H θ y i) x)=
      (∑l,partialAt T (.inl l)*derivativeMatrix (H l) x i k)+
      ∑α,partialAt T (.inr α)*halfDiff k (θ α) x := by
  rw [linear_apply_coordinates,Fintype.sum_sum_type]
  simp only [flipHalfDiff_coordinate,partialAt,localArgs,Sum.elim_inl,Sum.elim_inr,derivativeMatrix,mul_comm]

omit [DecidableEq ι] [DecidableEq κ] in
lemma local_argument_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n) :
    ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ ≤
      (∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (Finset.sum_nonneg fun l _=>abs_nonneg _) (Finset.sum_nonneg fun α _=>abs_nonneg _))).mpr
  intro l
  rw [Real.norm_eq_abs,flipHalfDiff_coordinate]
  cases l with
  | inl l =>
    dsimp only [localArgs,Sum.elim_inl]
    exact (Finset.single_le_sum (fun l _=>abs_nonneg (derivativeMatrix (H l) x i k)) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun α _=>abs_nonneg _))
  | inr α =>
    dsimp only [localArgs,Sum.elim_inr]
    exact (Finset.single_le_sum (fun α _=>abs_nonneg (halfDiff k (θ α) x)) (Finset.mem_univ α)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun l _=>abs_nonneg _))

lemma source_derivative_exact (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (i k : Fin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x i k=
      coefficient H θ F x i*derivativeMatrix s x i k+
      (∑l,s x i*localPartial H θ F' (.inl l) x i*derivativeMatrix (H l) x i k)+
      (∑α,s x i*localPartial H θ F' (.inr α) x i*halfDiff k (θ α) x)+
      s x i*taylorError H θ F F' x i k-
      2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k := by
  dsimp only [taylorError,localPartial]
  rw [coefficient_chain]
  simp only [←Finset.mul_sum,mul_assoc]
  rw [derivativeMatrix,halfDiff_mul]
  dsimp only [derivativeMatrix]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma taylor_error_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) {L Q T : ℝ} (hL : 0≤L) (hQ : 0≤Q) (hT : 0≤T)
    (hargs : ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖≤Q+T)
    (hF : ∀t∈Set.Icc (0:ℝ) 1,HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hLip : ∀t∈Set.Icc (0:ℝ) 1,
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
        F' i (localArgs H θ x i)‖≤L*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖) :
    |taylorError H θ F F' x i k|≤4*L*(Q^2+Q*T+T^2) := by
  have h:=coefficient_taylor k (fun y=>localArgs H θ y i) x (F i) (F' i) hL hF hLip
  have hs:=(pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hQ hT)
    (by decide : 2 ≠ 0)).2 hargs
  have hh:=mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hL)
  change |taylorError H θ F F' x i k|≤_ at h
  refine h.trans (hh.trans ?_)
  nlinarith [sq_nonneg Q,sq_nonneg T,mul_nonneg hL (sq_nonneg Q),mul_nonneg hL (sq_nonneg T)]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions_rf9a960_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma real_op_norm_nonneg (P : Matrix ι ι ℝ) : 0≤opNorm P := norm_nonneg _

lemma cauchy_bound {α : Type*} [Fintype α] (f g : α→ℝ) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hf : (∑i,(f i)^2)≤A^2) (hg : (∑i,(g i)^2)≤B^2) :
    |∑i,f i*g i|≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hh:=mul_le_mul hf hg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)
  nlinarith [sq_abs (∑i,f i*g i),mul_nonneg hA hB,abs_nonneg (∑i,f i*g i)]

omit [DecidableEq ι] in
lemma double_cauchy (f g : ι→ι→ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : (∑i,∑k,(f i k)^2)≤A^2) (hg : (∑i,∑k,(g i k)^2)≤B^2) :
    |∑i,∑k,f i k*g i k|≤A*B := by
  have H:=cauchy_bound (fun a : ι×ι=>f a.1 a.2) (fun a=>g a.1 a.2) hA hB
    (by simpa only [Fintype.sum_prod_type] using hf) (by simpa only [Fintype.sum_prod_type] using hg)
  simpa only [Fintype.sum_prod_type] using H

omit [DecidableEq ι] in
lemma trace_le_traceAbsolute (P E : Matrix ι ι ℝ) : |trace (P*E)|≤traceAbsolute P E := by
  rw [trace_mul_comm]
  simp only [trace,diag,Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum; intro i _
  exact (Finset.abs_sum_le_sum_abs ..).trans_eq (by simp only [abs_mul,mul_comm])

lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

lemma small_column_square (P : Matrix ι ι ℝ) (s : ι→ℝ) :
    (∑i,∑k,(|P k i| * |s i|)^2)≤(opNorm P)^2*(∑i,(s i)^2) := by
  simp only [mul_pow,sq_abs]
  calc
    _ ≤ ∑i,(opNorm P)^2*(s i)^2 := by
      apply Finset.sum_le_sum; intro i _
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (matrix_column_square_le P i) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]

lemma small_row_square (P : Matrix ι ι ℝ) (t : ι→ℝ) :
    (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P)^2*(∑k,(t k)^2) := by
  rw [Finset.sum_comm]
  simpa only [Matrix.transpose_apply,opNorm_transpose] using small_column_square Pᵀ t

lemma quadratic_trace_bound (P Q : Matrix ι ι ℝ) (s : ι→ℝ) {S B : ℝ}
    (hS : 0≤S) (hB : 0≤B) (hs : (∑i,(s i)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤B^4) :
    (∑i,∑k,|P k i| * |s i| *(Q i k)^2)≤opNorm P*S*B^2 := by
  have H:=double_cauchy (fun i k=>|P k i| * |s i|) (fun i k=>(Q i k)^2)
    (mul_nonneg (real_op_norm_nonneg P) hS) (pow_nonneg hB 2)
    ((small_column_square P s).trans (by
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hs (sq_nonneg (opNorm P))))
    (by simpa only [←pow_mul] using hQ)
  exact (le_abs_self _).trans H

lemma mixed_trace_bound (P Q : Matrix ι ι ℝ) (s t : ι→ℝ) {S T B : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ : ∀i,(∑k,(Q i k)^2)≤B^2) :
    (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)≤opNorm P*T*(S*B) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |Q i k|)^2)≤(S*B)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum]
    calc
      _ ≤ ∑i,(s i)^2*B^2 := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hQ i) (sq_nonneg _))
      _ = (∑i,(s i)^2)*B^2 := (Finset.sum_mul ..).symm
      _ ≤ S^2*B^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |Q i k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hB) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact H

lemma parameter_square_trace_bound (P : Matrix ι ι ℝ) (s t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |s i| *(t k)^2)≤opNorm P*T*(S*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |t k|)^2)≤(S*T)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum,←Finset.sum_mul]
    exact mul_le_mul hs ht (Finset.sum_nonneg (fun k _=>sq_nonneg _)) (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |t k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hT) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * (t k)^2) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    rw [← sq_abs (t k)]; ring
  rw [he]
  exact H

theorem source_taylor_trace_bound (P E Q : Matrix ι ι ℝ) (s t : ι→ℝ) {C S T B R : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ4 : (∑i,∑k,(Q i k)^4)≤B^4) (hQr : ∀i,(∑k,(Q i k)^2)≤R^2)
    (hE : ∀i k,|E i k|≤C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) :
    |trace (P*E)|≤C*opNorm P*S*(B^2+R*T+T^2) := by
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |s i| *(Q i k)^2)+
      (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)+
      (∑i,∑k,|P k i| * |s i| *(t k)^2)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*S*B^2+opNorm P*T*(S*R)+opNorm P*T*(S*T)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (quadratic_trace_bound P Q s hS hB hs hQ4)
        (mixed_trace_bound P Q s t hS hT hR hs ht hQr))
        (parameter_square_trace_bound P s t hS hT hs ht)) hC
    _ = _ := by ring

omit [DecidableEq ι] in
lemma fourth_holder (P D Q : Matrix ι ι ℝ) {B S R : ℝ}
    (hB : 0≤B) (hS : 0≤S) (hR : 0≤R)
    (hP : (∑i,∑k,(P i k)^4)≤B^4) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) :
    (∑i,∑k,|P i k| * |D i k| * |Q i k|)≤S*(B*R) := by
  have H₁:=double_cauchy (fun i k=>(P i k)^2) (fun i k=>(Q i k)^2)
    (sq_nonneg B) (sq_nonneg R) (by simpa only [←pow_mul] using hP)
    (by simpa only [←pow_mul] using hQ)
  have H₂ : (∑i,∑k,(|P i k| * |Q i k|)^2)≤(B*R)^2 := by
    simp only [mul_pow,sq_abs]
    exact (le_abs_self _).trans H₁
  have H₃:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P i k| * |Q i k|)
    hS (mul_nonneg hB hR) (by simpa only [sq_abs] using hD) H₂
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P i k| * |D i k| * |Q i k|) =
      ∑i,∑k,|D i k| * (|P i k| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H₃

lemma sum_split_diagonal (f : ι→ι→ℝ) :
    (∑i,∑k,f i k)=(∑i,f i i)+(∑i,∑k,if i=k then 0 else f i k) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  have he : f i i=∑k,if i=k then f i k else 0 := by simp
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs <;> simp

lemma diagonal_product_trace_bound (P D Q : Matrix ι ι ℝ) {S R : ℝ}
    (hS : 0≤S) (hR : 0≤R) (hD : (∑i,(D i i)^2)≤S^2)
    (hQ : (∑i,(Q i i)^2)≤R^2) :
    (∑i,|P i i| * |D i i| * |Q i i|)≤opNorm P*(S*R) := by
  calc
    _ ≤ ∑i,opNorm P*(|D i i| * |Q i i|) := by
      apply Finset.sum_le_sum; intro i _
      nlinarith [mul_le_mul_of_nonneg_right (matrix_entry_le_opNorm P i i)
        (mul_nonneg (abs_nonneg (D i i)) (abs_nonneg (Q i i)))]
    _ = opNorm P*(∑i,|D i i| * |Q i i|) := by rw [Finset.mul_sum]
    _ ≤ opNorm P*(S*R) := by
      apply mul_le_mul_of_nonneg_left _ (real_op_norm_nonneg P)
      exact (le_abs_self _).trans (cauchy_bound (fun i=>|D i i|) (fun i=>|Q i i|)
        hS hR (by simpa only [sq_abs] using hD) (by simpa only [sq_abs] using hQ))

lemma parameter_product_trace_bound (P D : Matrix ι ι ℝ) (t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |D i k| * |t k|)≤S*(opNorm P*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using
      (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have H:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P k i| * |t k|)
    hS (mul_nonneg (real_op_norm_nonneg P) hT) (by simpa only [sq_abs] using hD) hf
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |D i k| * |t k|) =
      ∑i,∑k,|D i k| * (|P k i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H

theorem source_product_trace_bound (P E D Q : Matrix ι ι ℝ) (t : ι→ℝ) {C S T B R L : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hD : (∑i,∑k,(D i k)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤B^4)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) (hQd : (∑i,(Q i i)^2)≤L^2)
    (hE : ∀i k,|E i k|≤C*|D i k| *(|Q i k|+|t k|)) :
    |trace (P*E)|≤C*S*(B*R+opNorm P*(L+T)) := by
  have hDd : (∑i,(D i i)^2)≤S^2 := by
    apply le_trans _ hD
    exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (D i k))
      (Finset.mem_univ i))
  let O : Matrix ι ι ℝ := fun i k=>if i=k then 0 else P k i
  have hO : (∑i,∑k,(O i k)^4)≤B^4 := by
    simpa only [O,ite_pow,zero_pow (by decide : 4≠0)] using hP
  have hOff := fourth_holder O D Q hB hS hR hO hD hQ
  have heOff : (∑i,∑k,if i=k then 0 else |P k i| * |D i k| * |Q i k|) =
      ∑i,∑k,|O i k| * |D i k| * |Q i k| := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    dsimp only [O]; split_ifs <;> simp
  have hProd : (∑i,∑k,|P k i| * |D i k| * |Q i k|)≤opNorm P*(S*L)+S*(B*R) := by
    rw [sum_split_diagonal,heOff]
    exact add_le_add (diagonal_product_trace_bound P D Q hS hL hDd hQd) hOff
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|D i k| *(|Q i k|+|t k|)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |D i k| * |Q i k|)+
        (∑i,∑k,|P k i| * |D i k| * |t k|)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*(S*L)+S*(B*R)+S*(opNorm P*T)) :=
      mul_le_mul_of_nonneg_left (add_le_add hProd
        (parameter_product_trace_bound P D t hS hT hD ht)) hC
    _ = _ := by ring

lemma rank_one_trace_bound (P : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |trace (P*Matrix.of (fun i k=>u i*v k))|≤opNorm P*‖u‖*‖v‖ := by
  have H:=abs_real_inner_le_norm v (P.toEuclideanLin.toContinuousLinearMap u)
  have he : trace (P*Matrix.of (fun i k=>u i*v k))=
      inner ℝ v (P.toEuclideanLin.toContinuousLinearMap u) := by
    change (∑i,∑k,P i k*(u k*v i))=∑i,(∑k,P i k*u k)*v i
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  apply H.trans
  have h:=mul_le_mul_of_nonneg_left
    (P.toEuclideanLin.toContinuousLinearMap.le_opNorm u) (norm_nonneg v)
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤opNorm P*‖u‖*‖v‖
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤‖v‖*(opNorm P*‖u‖) at h
  nlinarith only [h]

end SKGap.SourceError

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

lemma vectorNorm_mul (a s : Fin n→ℝ) {A : ℝ} (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) :
    vectorNorm (fun i=>a i*s i) ≤ A*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (vectorNorm_nonneg _))
  simp only [←sq,vectorNorm_sq,mul_pow]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
    (by nlinarith [sq_abs (a i),ha i,abs_nonneg (a i)]) (sq_nonneg _)

lemma row_scaled_frobenius (D : Interaction n) (s : Fin n→ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hD : ∀i,∑k,(D i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>s i*D i k)‖ ≤ R*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (vectorNorm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,vectorNorm_sq]
  simp only [Matrix.of_apply,mul_pow,←Finset.mul_sum]
  calc
    _  ≤  ∑i,(s i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; ring

lemma row_entry_bound (D : Interaction n) {R : ℝ} (hR : 0 ≤ R)
    (hD : ∀i,∑k,(D i k)^2 ≤ R^2) (i k : Fin n) : |D i k| ≤ R := by
  have H: (D i k)^2 ≤ R^2 :=
    (Finset.single_le_sum (fun l _=>sq_nonneg (D i l)) (Finset.mem_univ k)).trans (hD i)
  nlinarith [sq_abs (D i k),abs_nonneg (D i k)]

lemma multiplier_frobenius (a : Fin n→ℝ) (D : Interaction n) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) : ‖Matrix.of (fun i k=>a i*D i k)‖ ≤ A*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (norm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2) (sq_nonneg _)

lemma product_remainder_frobenius (A D : Interaction n) (x : Spin n) {R : ℝ}
    (hR : 0 ≤ R) (hA : ∀i,∑k,(A i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>2*spin x k*A i k*D i k)‖ ≤ 2*R*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,spin_sq,mul_one,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  have H:=row_entry_bound A hR hA i k
  have HH : (A i k)^2 ≤ R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i k)) H 2
  nlinarith [mul_nonneg (sq_nonneg (D i k)) (sub_nonneg.mpr HH)]

lemma source_derivative_product (a s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>a x i*s x i) x=
      (fun i k=>a x i*derivativeMatrix s x i k)+
      (fun i k=>s x i*derivativeMatrix a x i k)-
      (fun i k=>2*spin x k*derivativeMatrix a x i k*derivativeMatrix s x i k) := by
  ext i k
  exact halfDiff_mul k (fun x=>a x i) (fun x=>s x i) x

lemma source_frobenius (a s : VectorFields n) (x : Spin n) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (ha : ∀i,|a x i| ≤ A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2 ≤ R^2) :
    ‖derivativeMatrix (fun x i=>a x i*s x i) x‖ ≤
      A*‖derivativeMatrix s x‖+R*vectorNorm (s x)+2*R*‖derivativeMatrix s x‖ := by
  rw [source_derivative_product]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (multiplier_frobenius _ _ hA ha)
      (row_scaled_frobenius _ _ hR hda))) (product_remainder_frobenius _ _ x hR hda))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_sum {ι : Type*} [Fintype ι] (u : ι→Fin n→ℝ) :
    vectorNorm (∑l,u l) ≤ ∑l,vectorNorm (u l) := by
  change ‖(WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))‖≤_
  have he : (WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))=∑l,WithLp.toLp 2 (u l) := by
    ext i; simp [Finset.sum_apply]
  rw [he]
  exact norm_sum_le _ _

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma vectorNorm_matrix_mul (J : Interaction n) (u : Fin n→ℝ) :
    vectorNorm (J.mulVec u) ≤ SKGap.opNorm J*vectorNorm u := by
  exact (Matrix.toEuclideanCLM (𝕜:=ℝ) J).le_opNorm (WithLp.toLp 2 u)

lemma siteMean_square (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*(siteMean U x)^2 ≤ (vectorNorm (U x))^2 := by
  have H:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=U x)
  simp only [Finset.card_univ,Fintype.card_fin] at H
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  dsimp only [siteMean]
  rw [div_pow,vectorNorm_sq]
  apply (mul_le_mul_iff_left₀ hnR).mp
  field_simp
  nlinarith

lemma primary_mean_size (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    (hm : ∀i,|m x i|≤1) :
    vectorNorm (fun i=>siteMean U x*m x i) ≤ vectorNorm (U x) := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,(siteMean U x)^2 := by
      apply Finset.sum_le_sum; intro i _
      have H : (m x i)^2≤1 := by
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (m x i)) (hm i) 2
      nlinarith [sq_nonneg (siteMean U x)]
    _ = (n:ℝ)*(siteMean U x)^2 := by simp
    _ ≤ _ := by simpa only [vectorNorm_sq] using siteMean_square U x hn

lemma scaled_frobenius_by_rows (D : Interaction n) (a : ℝ) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (ha : (n:ℝ)*a^2≤C^2)
    (hD : ∀i,∑k,(D i k)^2≤P^2) : ‖a • D‖≤C*P := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hP)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,a^2*P^2 := Finset.sum_le_sum fun i _=>by
      rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = ((n:ℝ)*a^2)*P^2 := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)

lemma primary_mean_frobenius (U m : VectorFields n) (x : Spin n) (hn : 0<n) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (hu : vectorNorm (U x)≤C) (hdu : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x‖≤C*(1+3*P) := by
  have hav : (n:ℝ)*(siteMean U x)^2≤C^2 := (siteMean_square U x hn).trans
    (pow_le_pow_left₀ (vectorNorm_nonneg _) hu 2)
  have hdav : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hdu)
  have hs := scaled_frobenius_by_rows (derivativeMatrix m x) (siteMean U x) hC hP hav (fun i=>
    (SKGap.SourceError.matrix_row_square_le _ i).trans (pow_le_pow_left₀ (norm_nonneg _) hdm 2))
  have he := product_derivative_error hn hC hdm hm hdav
  calc
    _ ≤ ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x-siteMean U x • derivativeMatrix m x‖+
      ‖siteMean U x • derivativeMatrix m x‖ := norm_le_norm_sub_add _ _
    _ ≤ (C+2*P*C)+C*P := add_le_add he hs
    _ = _ := by ring

lemma coefficient_mean_value (a : VectorFields n) (x : Spin n) {A : ℝ}
    (hA : 0≤A) (ha : ∀i,|a x i|≤A) : |siteMean a x|≤A := by
  by_cases hn : n=0
  · subst n; simp [siteMean,hA]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [siteMean,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑i,|a x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i:Fin n,A := Finset.sum_le_sum fun i _=>ha i
    _ = _ := by simp [mul_comm]

lemma coefficient_mean_difference (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    ‖derivativeVector (siteMean a) x‖≤R := by
  have he : derivativeVector (siteMean a) x = (n:ℝ)⁻¹ •
      ∑i,WithLp.toLp 2 (fun k=>derivativeMatrix a x i k) := by
    ext k
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp]
    simp only [halfDiff,siteMean,derivativeMatrix]
    rw [←Finset.sum_div,Finset.sum_sub_distrib]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · subst n; simp [hR]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    _ ≤ (n:ℝ)⁻¹*(∑_i:Fin n,R) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>by
        apply nonneg_le_nonneg_of_sq_le_sq hR
        simpa only [←sq,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hda i)) (inv_nonneg.mpr hnR.le)
    _ = R := by simp [hnR.ne']

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_CoefficientRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma row_vectorNorm_le_opNorm (D : Interaction n) (i : Fin n) :
    vectorNorm (D i) ≤ SKGap.opNorm D := by
  have h0 : 0≤SKGap.opNorm D := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq h0
  simp only [←sq,vectorNorm_sq]
  exact SKGap.SourceError.matrix_row_square_le D i

lemma local_argument_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (x : Spin n) (i : Fin n) :
    vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) ≤
      (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖) := by
  have hQ (l : ι) : vectorNorm (fun k=>|derivativeMatrix (H l) x i k|)≤SKGap.opNorm (derivativeMatrix (H l) x) := by
    rw [vectorNorm_abs]; exact row_vectorNorm_le_opNorm _ _
  have hT (α : κ) : vectorNorm (fun k=>|halfDiff k (θ α) x|)=‖derivativeVector (θ α) x‖ := by
    rw [vectorNorm_abs]; rfl
  calc
    _ ≤ vectorNorm (fun k=>(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|)) :=
      vectorNorm_mono fun k=>by
        have hp : 0≤(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) :=
          add_nonneg (Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.sum_nonneg fun _ _=>abs_nonneg _)
        simpa only [abs_of_nonneg (norm_nonneg _),abs_of_nonneg hp] using local_argument_bound H θ x i k
    _ ≤ vectorNorm (fun k=>∑l,|derivativeMatrix (H l) x i k|)+
        vectorNorm (fun k=>∑α,|halfDiff k (θ α) x|) := vectorNorm_add _ _
    _ ≤ (∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|))+
        ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      apply add_le_add
      · convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
      · convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun l _=>hQ l) (by simp only [hT]; rfl)

lemma coefficient_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i : Fin n) {L : ℝ} (hL : 0≤L)
    (hF : ∀k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hBound : ∀k t, t∈Set.Icc (0:ℝ) 1→
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤L) :
    vectorNorm (derivativeMatrix (coefficient H θ F) x i) ≤
      L*((∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>L*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
        exact coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i) hL (hF k) (hBound k)
    _ = L*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul L (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_of_nonneg hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) hL

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma derivativeMatrix_add (U V : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>U x i+V x i) x=derivativeMatrix U x+derivativeMatrix V x := by
  ext i k; simp only [derivativeMatrix,halfDiff,Matrix.add_apply]; ring

lemma derivativeMatrix_sum {ι : Type*} [Fintype ι] (U : ι→VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>∑l,U l x i) x=∑l,derivativeMatrix (U l) x := by
  ext i k; simp only [Matrix.sum_apply,derivativeMatrix,halfDiff_sum]

lemma SmallBound.mono {U : VectorFields n} {x : Spin n} {C D : ℝ}
    (h : SmallBound U x C) (hCD : C≤D) : SmallBound U x D :=
  ⟨h.nonneg.trans hCD,h.size.trans hCD,h.derivative.trans hCD⟩

lemma SmallBound.seed (s : Fin n→ℝ) (x : Spin n) :
    SmallBound (fun _=>s) x (vectorNorm s) := by
  refine ⟨vectorNorm_nonneg _,le_rfl,?_⟩
  have he : derivativeMatrix (fun _=>s) x=0 := by ext i k; simp [derivativeMatrix,halfDiff]
  rw [he,norm_zero]; exact vectorNorm_nonneg _

lemma SmallBound.add {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i+V x i) x (C+D) := by
  refine ⟨add_nonneg hU.nonneg hV.nonneg,(vectorNorm_add _ _).trans (add_le_add hU.size hV.size),?_⟩
  rw [derivativeMatrix_add]
  exact (norm_add_le _ _).trans (add_le_add hU.derivative hV.derivative)

lemma SmallBound.smul {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (c : ℝ) : SmallBound (fun x i=>c*U x i) x (|c| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hU.nonneg,?_,?_⟩
  · calc
      _ = |c| *vectorNorm (U x) := vectorNorm_smul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hU.size (abs_nonneg _)
  · rw [derivativeMatrix_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hU.derivative (abs_nonneg _)

lemma SmallBound.sub {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i-V x i) x (C+D) := by
  simpa only [abs_neg,abs_one,one_mul,neg_one_mul,sub_eq_add_neg] using hU.add (hV.smul (-1))

lemma SmallBound.sum {ι : Type*} [Fintype ι] {U : ι→VectorFields n} {x : Spin n} {C : ι→ℝ}
    (hU : ∀l,SmallBound (U l) x (C l)) :
    SmallBound (fun x i=>∑l,U l x i) x (∑l,C l) := by
  refine ⟨Finset.sum_nonneg fun l _=>(hU l).nonneg,?_,?_⟩
  · have h:= (vectorNorm_sum (fun l=>U l x)).trans (Finset.sum_le_sum fun l _=>(hU l).size)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; ext i; simp
  · rw [derivativeMatrix_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _=>(hU l).derivative)

lemma SmallBound.coefficient {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,?_⟩
  · exact ((vectorNorm_mul _ _ hA ha).trans (mul_le_mul_of_nonneg_left hU.size hA)).trans
      (by nlinarith [mul_nonneg hU.nonneg hR])
  · calc
      _ ≤ A*‖derivativeMatrix U x‖+R*vectorNorm (U x)+2*R*‖derivativeMatrix U x‖ :=
        source_frobenius a U x hA hR ha hda
      _ ≤ A*C+R*C+2*R*C := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hU.derivative hA) (mul_le_mul_of_nonneg_left hU.size hR))
        (mul_le_mul_of_nonneg_left hU.derivative (by positivity))
      _ = _ := by ring

lemma SmallBound.linear {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (J : Interaction n) :
    SmallBound (fun x=>J.mulVec (U x)) x (SKGap.opNorm J*C) := by
  refine ⟨mul_nonneg (norm_nonneg _) hU.nonneg,
    (vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_left hU.size (norm_nonneg _)),?_⟩
  have he : derivativeMatrix (fun x=>J.mulVec (U x)) x=J*derivativeMatrix U x := by
    convert! derivativeMatrix_linear J U (fun _=>0) x using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_add]; rfl
  rw [he]
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hU.derivative (norm_nonneg _))

lemma SmallBound.primaryCorrection {U : VectorFields n} {x : Spin n} {C P : ℝ}
    (hU : SmallBound U x C) (m : VectorFields n) (hn : 0<n) (hP : 0≤P)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    SmallBound (fun y i=>siteMean U y*m y i) x (C*(1+3*P)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,
    primary_mean_frobenius U m x hn hU.nonneg hP hU.size hU.derivative hm hdm⟩
  exact ((primary_mean_size U m x hn hm).trans hU.size).trans (by nlinarith [mul_nonneg hU.nonneg hP])

lemma SmallBound.auxiliaryCorrection {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun y i=>siteMean a y*U y i) x (C*(A+3*R)) := by
  apply hU.coefficient (fun x _=>siteMean a x) hA hR (fun _=>coefficient_mean_value a x hA ha)
  intro i
  have H:=pow_le_pow_left₀ (norm_nonneg _) (coefficient_mean_difference a x hR hda) 2
  simpa only [derivativeMatrix,derivativeVector,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using H

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_OrdinaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma CoefficientBound.small_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) :=
  hU.coefficient a ha.size_nonneg ha.row_nonneg ha.value ha.difference

lemma CoefficientBound.mean_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>siteMean a x*U x i) x (C*(A+3*R)) :=
  hU.auxiliaryCorrection a ha.size_nonneg ha.row_nonneg ha.value ha.difference

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma sourceOf_bound (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.sourceOf a Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [←Finset.sum_mul,add_mul]

lemma partialOf_bound (a : ℕ) (l : ι) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedPartial a l s) x A R)
    (ha : ∀b,CoefficientBound (D.auxPartial a l b) x A R) :
    SmallBound (D.partialOf a l Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [←Finset.sum_mul,add_mul]

lemma fieldOf_bound (a : ℕ) (W Y : Fin a→VectorFields n) (x : Spin n) (hn : 0<n)
    {A R L P C : ℝ} (B : Fin a→ℝ) (hL : 0≤L) (hP : 0≤P) (hJ : SKGap.opNorm D.J≤L)
    (hw : SmallBound (D.sourceOf a Y) x C)
    (hp : ∀l,SmallBound (D.partialOf a l Y) x C)
    (hW : ∀b,SmallBound (W b) x (B b))
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.fieldOf a W Y) x
      ((L*C+|D.j| *((Fintype.card ι:ℝ)*(C*(1+3*P))))+|D.j| *((∑b,B b)*(A+3*R))) := by
  have h0 := (hw.linear D.J).mono (mul_le_mul hJ le_rfl hw.nonneg hL)
  have h1 := (SmallBound.sum fun l=>(hp l).primaryCorrection (D.predecessor l) hn hP (hm l) (hdm l)).smul D.j
  have h2 := (SmallBound.sum fun b=>(ha b).mean_product (hW b)).smul D.j
  have H:= (h0.sub h1).sub h2
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul]

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_RecipeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix

lemma recipeCost_nonneg {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    0 ≤ recipeCost A R L P j d := by unfold recipeCost; positivity

lemma recipeCost_ge {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    A+3*R ≤ recipeCost A R L P j d := by
  have hT : 0≤A+3*R := by positivity
  have hd : 0≤|j| *((d:ℝ)*(1+3*P)+1) := by positivity
  unfold recipeCost
  nlinarith [mul_nonneg hT hL,mul_nonneg hT hd]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma SegmentRegular.partial_bound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (i : Fin n) (l : ι⊕κ) :
    |localPartial H θ F' l x i|≤C := by
  have hb : ‖F' i (localArgs H θ x i)‖≤C := by simpa using h.bound i i 0 (by constructor <;> norm_num)
  have hs : ‖(Pi.single l (1:ℝ) : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have h₁ := (F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  exact h₁.trans ((mul_le_mul hb hs (norm_nonneg _) h.nonneg).trans_eq (mul_one C))

lemma sourceError_eq (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    sourceError H θ F F' s x=
      (∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))+
      Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k) := by
  ext i k
  simp only [sourceError,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.sum_apply,Matrix.add_apply,Matrix.of_apply]
  rw [source_derivative_exact]
  ring

lemma sourceError_trace (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (P : Interaction n) {C S T B R L O : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hR : 0≤R) (hL : 0≤L) (hO : 0≤O)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤O^4) :
    |trace (P*sourceError H θ F F' s x)|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖)+
      4*C*SKGap.opNorm P*S*(B^2+R*T+T^2)+
      2*C*S*(O*B+SKGap.opNorm P*(L+T)) := by
  let Q := primaryIncrement H x
  let t := parameterIncrement θ x
  have hQ : ∀i k,0≤Q i k := fun i k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have htt : ∀k,0≤t k := fun k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hs2 : (∑i,(s x i)^2)≤S^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) hs 2
  have ht2 : (∑k,(t k)^2)≤T^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) ht 2
  have hds2 : (∑i,∑k,(derivativeMatrix s x i k)^2)≤S^2 := by
    rw [←SKGap.frobenius_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hds 2
  have htaylor := source_taylor_trace_bound P (Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)) Q (s x) t
    (mul_nonneg (by norm_num : (0:ℝ)≤4) h.nonneg) hS hT hB hR hs2 ht2 hQ4 hQr (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      have hh := taylor_error_bound H θ F F' x i k h.nonneg (hQ i k) (htt k)
        (local_argument_bound H θ x i k) (h.deriv i k) (h.lip i k)
      nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (s x i))])
  have hproduct := source_product_trace_bound P
    (Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k))
    (derivativeMatrix s x) Q t (mul_nonneg (by norm_num : (0:ℝ)≤2) h.nonneg)
    hS hT hO hB hL hds2 ht2 hP hQ4 hQd (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh := (coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i)
        h.nonneg (h.deriv i k) (h.bound i k)).trans
          (mul_le_mul_of_nonneg_left (local_argument_bound H θ x i k) h.nonneg)
      change |derivativeMatrix (coefficient H θ F) x i k|≤C*(Q i k+t k) at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (derivativeMatrix s x i k))])
  have hrank (α : κ) :
      |trace (P*Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))|≤
        SKGap.opNorm P*C*S*‖derivativeVector (θ α) x‖ := by
    have hu : vectorNorm (fun i=>s x i*localPartial H θ F' (.inr α) x i)≤C*S := by
      have H₁ := (vectorNorm_mul (fun i=>localPartial H θ F' (.inr α) x i) (s x) h.nonneg
        (fun i=>h.partial_bound i (.inr α))).trans (mul_le_mul_of_nonneg_left hs h.nonneg)
      simpa only [mul_comm] using H₁
    have HH:=rank_one_trace_bound P
      (WithLp.toLp 2 (fun i=>s x i*localPartial H θ F' (.inr α) x i)) (derivativeVector (θ α) x)
    apply HH.trans
    change SKGap.opNorm P*vectorNorm _*‖derivativeVector (θ α) x‖≤_
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (real_op_norm_nonneg P))
      (norm_nonneg (derivativeVector (θ α) x))]
  have hranks : |trace (P*(∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x)))|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖) := by
    rw [Matrix.mul_sum,trace_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun α _=>hrank α).trans_eq (by rw [Finset.mul_sum]))
  rw [sourceError_eq,mul_sub,mul_add,trace_sub,trace_add]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hranks htaylor)) hproduct)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_RecipeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finite_sum_fourth (f : ι→ℝ) :
    (∑l,f l)^4≤(Fintype.card ι:ℝ)^3*∑l,(f l)^4 := by
  have h1:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=f)
  have h2:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun l=>(f l)^2)
  simp only [Finset.card_univ] at h1 h2
  have hsq:=pow_le_pow_left₀ (sq_nonneg (∑l,f l)) h1 2
  have hh:=mul_le_mul_of_nonneg_left h2 (sq_nonneg (Fintype.card ι:ℝ))
  simp only [←pow_mul] at hsq hh
  norm_num only [Nat.reduceMul] at hsq hh
  nlinarith only [hsq,hh]

lemma primaryIncrement_fourth (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,ShapeBound (derivativeMatrix (H l) x) P) :
    (∑i,∑k,(primaryIncrement H x i k)^4)≤(2*(Fintype.card ι:ℝ)*P)^4 := by
  have h1 : (∑i,∑k,(primaryIncrement H x i k)^4)≤
      (Fintype.card ι:ℝ)^3*∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4 := by
    calc
      _ ≤ ∑i,∑k,(Fintype.card ι:ℝ)^3*∑l,(derivativeMatrix (H l) x i k)^4 := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro k _
        simpa only [primaryIncrement,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using finite_sum_fourth (fun l=>|derivativeMatrix (H l) x i k|)
      _ = _ := by
        simp_rw [←Finset.mul_sum]
        congr 1
        rw [show (∑i,∑k,∑l,(derivativeMatrix (H l) x i k)^4)=
            ∑i,∑l,∑k,(derivativeMatrix (H l) x i k)^4 from
          Finset.sum_congr rfl (fun i _=>Finset.sum_comm)]
        exact Finset.sum_comm
  have h2 : (∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4)≤(Fintype.card ι:ℝ)*(2*P^4) := by
    exact (Finset.sum_le_sum (fun l _=>fourth_sum_le hP (hH l))).trans_eq (by simp)
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hnn : 0≤(Fintype.card ι:ℝ)^4*P^4 := by positivity
  nlinarith only [h3,hnn]

lemma primaryIncrement_row (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.opNorm (derivativeMatrix (H l) x)≤P) (i : Fin n) :
    (∑k,(primaryIncrement H x i k)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (primaryIncrement H x i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|) := by
        convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact (row_vectorNorm_le_opNorm _ _).trans (hH l)
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma primaryIncrement_diagonal (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.diagonalSeminorm (derivativeMatrix (H l) x)≤P) :
    (∑i,(primaryIncrement H x i i)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (fun i=>primaryIncrement H x i i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun i=>|derivativeMatrix (H l) x i i|) := by
        convert! vectorNorm_sum (fun l i=>|derivativeMatrix (H l) x i i|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext i; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact hH l
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma parameterIncrement_bound (θ : κ→Spin n→ℝ) (x : Spin n) :
    vectorNorm (parameterIncrement θ x)≤∑α,‖derivativeVector (θ α) x‖ := by
  calc
    _ ≤ ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1; ext k; simp [parameterIncrement]
    _ = _ := by apply Finset.sum_congr rfl; intro α _; rw [vectorNorm_abs]; rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
variable {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
variable {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
variable {x : Spin n} {C : ℝ}

lemma SegmentRegular.partial_difference (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) (i k : Fin n) :
    |derivativeMatrix (localPartial H θ F' l) x i k|≤
      C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ := by
  have hv : ‖(Pi.single l 1 : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have hh:=h.lip i k 1 (by constructor <;> norm_num)
  simp only [one_smul,add_sub_cancel] at hh
  have H₁ := (F' i (localArgs H θ (flip x k) i)-F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  have H₂ : |localPartial H θ F' l (flip x k) i-localPartial H θ F' l x i|≤
      C*‖localArgs H θ (flip x k) i-localArgs H θ x i‖ := by
    apply H₁.trans
    exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa only [mul_one] using hh)
  rw [derivativeMatrix,halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  exact (div_le_div_of_nonneg_right H₂ (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma SegmentRegular.partial_row (h : SegmentRegular H θ F F' x C) (l : ι⊕κ) (i : Fin n) :
    vectorNorm (derivativeMatrix (localPartial H θ F' l) x i)≤
      C*((∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg h.nonneg (norm_nonneg _))]
        exact h.partial_difference l i k
    _ = C*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul C (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_of_nonneg h.nonneg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) h.nonneg

omit [DecidableEq ι] [DecidableEq κ] in
lemma SegmentRegular.coefficient_bound (h : SegmentRegular H θ F F' x C)
    {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hv : ∀i,|coefficient H θ F x i|≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (coefficient H θ F) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,hv,?_⟩
  intro i
  have H₁ := (coefficient_row_bound H θ F F' x i h.nonneg (h.deriv i) (h.bound i)).trans
    (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

lemma SegmentRegular.partial_bound_coefficient (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hCA : C≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (localPartial H θ F' l) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,fun i=>(h.partial_bound i l).trans hCA,?_⟩
  intro i
  have H₁ := (h.partial_row l i).trans (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_CorrectionTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}

lemma trace_small_diagonal (P E : Interaction n) (u : Fin n→ℝ) :
    |trace (P*(Matrix.diagonal u*E))|≤SKGap.opNorm P*vectorNorm u*‖E‖ := by
  apply (trace_le_traceAbsolute P (Matrix.diagonal u*E)).trans
  have H := double_cauchy (fun i k=>|P k i| *|u i|) (fun i k=>|E i k|)
    (mul_nonneg (real_op_norm_nonneg P) (vectorNorm_nonneg u)) (norm_nonneg E)
    (by simpa only [mul_pow,vectorNorm_sq] using small_column_square P u)
    (by simpa only [sq_abs] using le_of_eq (SKGap.frobenius_sq E).symm)
  have HH := (le_abs_self (∑i,∑k,(|P k i| * |u i|)*|E i k|)).trans H
  simpa only [traceAbsolute,Matrix.diagonal_mul,abs_mul,mul_assoc] using HH

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_StartedRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

lemma startedSource_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedSource w y a=D.sourceOf a (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedSource,startedEvaluate];rfl
lemma startedAuxiliary_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedAuxiliary w y a=D.fieldOf a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedAuxiliary,startedEvaluate];rfl

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma testSize_nonneg (P : Interaction n) : 0≤testSize P := add_nonneg (norm_nonneg _) (norm_nonneg _)
lemma opNorm_le_testSize (P : Interaction n) : SKGap.opNorm P≤testSize P := le_add_of_nonneg_right (norm_nonneg _)

lemma TraceControl.mono {E : Interaction n} {C D : ℝ} (h : TraceControl E C) (hCD : C≤D) : TraceControl E D :=
  ⟨h.nonneg.trans hCD,fun P=>(h.bound P).trans (mul_le_mul_of_nonneg_right hCD (testSize_nonneg P))⟩
lemma TraceControl.add {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E+F) (C+D) := by
  refine ⟨add_nonneg hE.nonneg hF.nonneg,?_⟩
  intro P; rw [mul_add,trace_add,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hE.bound P) (hF.bound P))
lemma TraceControl.sum {α : Type*} [Fintype α] {E : α→Interaction n} {C : α→ℝ}
    (h : ∀a,TraceControl (E a) (C a)) : TraceControl (∑a,E a) (∑a,C a) := by
  refine ⟨Finset.sum_nonneg (fun a _=>(h a).nonneg),?_⟩
  intro P; rw [Matrix.mul_sum,trace_sum,Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun a _=>(h a).bound P)

lemma control_of_operator {E : Interaction n} {C : ℝ} (hC : 0≤C)
    (h : ∀P,|trace (P*E)|≤C*SKGap.opNorm P) : TraceControl E C :=
  ⟨hC,fun P=>(h P).trans (mul_le_mul_of_nonneg_left (opNorm_le_testSize P) hC)⟩

lemma small_diagonal_control (E : Interaction n) (u : Fin n→ℝ) :
    TraceControl (Matrix.diagonal u*E) (vectorNorm u*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_diagonal P E u).trans_eq (by ring)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma sourceError_control (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) {C S T B R L : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2) :
    TraceControl (sourceError H θ F F' s x)
      (C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(B+L+T))) := by
  have hC := h.nonneg
  have hsum : 0≤∑α,‖derivativeVector (θ α) x‖ := Finset.sum_nonneg fun α _=>norm_nonneg _
  refine ⟨by positivity,?_⟩
  intro P
  have hO : 0≤SKGap.offDiagonalSeminorm P := norm_nonneg _
  have hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤SKGap.offDiagonalSeminorm P^4 := by
    rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eq_comm]; rfl
  apply (sourceError_trace H θ F F' s x P h hS hT hB hR hL hO hs hds ht hQ4 hQr hQd hP).trans
  have h₁ : 0≤C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(L+T)) := by positivity
  have h₂ : 0≤2*C*S*B := by positivity
  have H₁ := mul_nonneg (real_op_norm_nonneg P) h₂
  have H₂ := mul_nonneg hO h₁
  unfold testSize
  nlinarith only [H₁,H₂]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Matrix_StartedNodeTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)

lemma startedNodeSource_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ)
    {C Q R L V Z : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : ∀b:Fin a,SmallBound (D.startedAuxiliary w y b) x (B b))
    (hp : ∀l,SmallBound (D.startedPartial w y a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖≤E l)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x C)
    (ha : ∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.startedNodeSourceError w y T x a)
      (((∑s,C*vectorNorm (D.seed s)*Z)+(∑b:Fin a,C*B b*Z))+∑l,Cp l*E l) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := TraceControl.sum (fun b:Fin a=>hc (D.startedAuxiliary w y b) (hY b) _ _ (ha b))
  have hp' := TraceControl.sum (fun l=>(small_diagonal_control
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)) (D.startedPartial w y a l x)).mono
      (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg))
  exact (hs'.add ha').add hp'

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Stability_OrdinaryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

namespace LocalConstants
variable (c : LocalConstants)
lemma A_nonneg : 0 ≤ c.A := le_trans (by norm_num) c.one_le_A
lemma argument_nonneg (d : ℕ) : 0 ≤ c.argument d := by unfold argument; positivity [c.P_nonneg,c.V_nonneg]
lemma row_nonneg (d : ℕ) : 0 ≤ c.row d := mul_nonneg c.C_nonneg (c.argument_nonneg d)
lemma traceCost_nonneg (d : ℕ) : 0 ≤ c.traceCost d := by unfold traceCost; positivity [c.P_nonneg,c.V_nonneg]
end LocalConstants

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants}
variable (h : LocalOrdinaryInput D T x N c)
include h

lemma argument_bound : (∑l,SKGap.opNorm (derivativeMatrix (D.H l) x))+
    (∑α,‖derivativeVector (D.θ α) x‖) ≤ c.argument (Fintype.card ι) := by
  apply add_le_add _ h.parameter
  exact (Finset.sum_le_sum fun l _=>(h.primaryShape l).1).trans_eq (by simp)
lemma seed_bound (a : ℕ) (ha : a≤N) (s : σ) :
    CoefficientBound (D.seedCoefficient a s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.seedValue a ha s) h.argument_bound
lemma aux_bound (a : ℕ) (ha : a≤N) (b : Fin a) :
    CoefficientBound (D.auxCoefficient a b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.auxValue a ha b) h.argument_bound
lemma seed_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (s : σ) :
    CoefficientBound (D.seedPartial a l s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound
lemma aux_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (b : Fin a) :
    CoefficientBound (D.auxPartial a l b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound

end LocalOrdinaryInput

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_StartedSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
variable {n : ℕ}

lemma startedBudget_nonneg {c S B : ℝ} (hc : 0 ≤ c) (hS : 0≤S) (hB : 0≤B) (a : ℕ) :
    0≤ startedBudget c S B a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [startedBudget]
    exact add_nonneg (mul_nonneg hc (add_nonneg hS (Finset.sum_nonneg fun b _=>ih b b.isLt))) hB
lemma startedBudget_ge {c S B : ℝ} (hc : 0 ≤ c) (hS : 0≤S) (hB : 0≤B) (a : ℕ) :
    B≤ startedBudget c S B a := by
  rw [startedBudget]
  exact le_add_of_nonneg_left (mul_nonneg hc (add_nonneg hS
    (Finset.sum_nonneg fun b _=>startedBudget_nonneg hc hS hB b)))

namespace OrdinaryData
open Primary Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

theorem started_evaluation_small (w y : VectorFields n) (N : ℕ) (x : Spin n) (hn : 0<n)
    {A R L P S B : ℝ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) (hS : 0≤S) (hB : 0≤B)
    (hw₀ : SmallBound w x B) (hy₀ : SmallBound y x B)
    (hJ : SKGap.opNorm D.J≤L) (hseed : (∑s,vectorNorm (D.seed s))≤S)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hs : ∀a≤N,∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀a≤N,∀b,CoefficientBound (D.auxCoefficient a b) x A R)
    (hsp : ∀a≤N,∀l s,CoefficientBound (D.seedPartial a l s) x A R)
    (hap : ∀a≤N,∀l b,CoefficientBound (D.auxPartial a l b) x A R) :
    ∀a≤N,
      SmallBound (D.startedSource w y a) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) ∧
      SmallBound (D.startedAuxiliary w y a) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) ∧
      ∀l,SmallBound (D.startedPartial w y a l) x (startedBudget (recipeCost A R L P D.j (Fintype.card ι)) S B a) := by
  let c:=recipeCost A R L P D.j (Fintype.card ι)
  have hc : 0 ≤ c:=recipeCost_nonneg hA hR hL hP
  have hT : 0≤A+3*R:=by positivity
  have hcg : A+3*R ≤ c:=recipeCost_ge hA hR hL hP
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    let V : Fin a→ℝ:=fun b=>startedBudget c S B b
    let I:=S+∑b,V b
    let Z:=I*(A+3*R)
    have hV : ∀b,0≤V b:=fun b=>startedBudget_nonneg hc hS hB b
    have hI : 0≤I:=add_nonneg hS (Finset.sum_nonneg fun b _=>hV b)
    have hY : ∀b:Fin a,SmallBound (D.startedAuxiliary w y b) x (V b):=
      fun b=>(ih b b.isLt (b.isLt.le.trans haN)).2.1
    have hW : ∀b:Fin a,SmallBound (D.startedSource w y b) x (V b):=
      fun b=>(ih b b.isLt (b.isLt.le.trans haN)).1
    have hw : SmallBound (D.sourceOf a (fun b=>D.startedAuxiliary w y b)) x Z:=
      (D.sourceOf_bound a _ x V hY (hs a haN) (ha a haN)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,V b)≤I from
          add_le_add hseed le_rfl) hT)
    have hp : ∀l,SmallBound (D.partialOf a l (fun b=>D.startedAuxiliary w y b)) x Z:=fun l=>
      (D.partialOf_bound a l _ x V hY (hsp a haN l) (hap a haN l)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,V b)≤I from
          add_le_add hseed le_rfl) hT)
    have hZ : Z≤ startedBudget c S B a:=by
      rw [startedBudget]
      exact (mul_le_mul_of_nonneg_left hcg hI).trans (by dsimp [I,V];nlinarith only [hB])
    have hf:=D.fieldOf_bound a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b)
      x hn V hL hP hJ hw hp hW hm hdm (ha a haN)
    have hfC : (L*Z+|D.j| *((Fintype.card ι:ℝ)*(Z*(1+3*P))))+
        |D.j| *((∑b,V b)*(A+3*R))≤ startedBudget c S B a:=by
      rw [startedBudget]
      change _ ≤ c*I+B
      dsimp [c,recipeCost,Z,I]
      have h1 : 0≤(S+∑b,V b)*(A+3*R):=mul_nonneg hI hT
      have h2 : 0≤|D.j| *(S*(A+3*R)):=mul_nonneg (abs_nonneg _) (mul_nonneg hS hT)
      nlinarith only [h1,h2,hB]
    refine ⟨?_,?_,fun l=>(hp l).mono hZ⟩
    · by_cases ha0:a=0
      · subst a;simpa using hw₀.mono (startedBudget_ge hc hS hB 0)
      · rw [D.startedSource_eq w y (by omega)];exact hw.mono hZ
    · by_cases ha0:a=0
      · subst a;simpa using hy₀.mono (startedBudget_ge hc hS hB 0)
      · rw [D.startedAuxiliary_eq w y (by omega)];exact hf.mono hfC

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants} {w y : VectorFields n} {B : ℝ}
variable (h : LocalOrdinaryInput D T x N c) (hB : 0≤B) (hw₀ : SmallBound w x B) (hy₀ : SmallBound y x B)
include h hB hw₀ hy₀

lemma started_small (a : ℕ) (ha : a≤N) :
    SmallBound (D.startedSource w y a) x (c.startedNormBudget D.j (Fintype.card ι) B a) ∧
    SmallBound (D.startedAuxiliary w y a) x (c.startedNormBudget D.j (Fintype.card ι) B a) ∧
    ∀l,SmallBound (D.startedPartial w y a l) x (c.startedNormBudget D.j (Fintype.card ι) B a) :=
  D.started_evaluation_small w y N x h.dimension c.A_nonneg (c.row_nonneg _) c.L_nonneg c.P_nonneg c.S_nonneg hB hw₀ hy₀
    h.interaction h.seed h.primaryValue h.primaryDerivative h.seed_bound h.aux_bound h.seed_partial_bound h.aux_partial_bound a ha

lemma started_source_control_s2_oai (a : ℕ) (ha : a≤N) :
    TraceControl (D.startedNodeSourceError w y T x a) (c.startedSourceCost D.j (Fintype.card ι) (Fintype.card σ) B a) := by
  let d:=Fintype.card ι
  let W:=c.startedNormBudget D.j d B
  have hn (s : σ) : vectorNorm (D.seed s) ≤ c.S :=
    (Finset.single_le_sum (fun s _=>vectorNorm_nonneg (D.seed s)) (Finset.mem_univ s)).trans h.seed
  have H:=D.startedNodeSource_control w y T x a c.C_nonneg
    (show 0≤2*(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg]) c.V_nonneg
    (fun b:Fin a=>(h.started_small hB hw₀ hy₀ b (b.isLt.le.trans ha)).2.1) (h.started_small hB hw₀ hy₀ a ha).2.2 h.primaryFieldError
    (h.seedRegular a ha) (h.auxRegular a ha)
    ((parameterIncrement_bound D.θ x).trans h.parameter)
    (primaryIncrement_fourth D.H x c.P_nonneg h.primaryShape)
    (primaryIncrement_row D.H x c.P_nonneg (fun l=>(h.primaryShape l).1))
    (primaryIncrement_diagonal D.H x c.P_nonneg (fun l=>(h.primaryShape l).2.1))
    (show _ ≤ c.traceCost d from add_le_add (add_le_add h.parameter le_rfl) le_rfl)
  apply H.mono
  have hs : (∑s,c.C*vectorNorm (D.seed s)*c.traceCost d)≤(Fintype.card σ:ℝ)*(c.C*c.S*c.traceCost d) :=
    (Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hn s) c.C_nonneg) (c.traceCost_nonneg d)).trans_eq (by simp)
  dsimp only [LocalConstants.startedSourceCost]
  have hp : (∑_l:ι,c.startedNormBudget D.j d B a*c.E)=(d:ℝ)*(c.startedNormBudget D.j d B a*c.E) := by simp [d]
  rw [hp]
  exact add_le_add (add_le_add hs le_rfl) le_rfl

end LocalOrdinaryInput
end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SKGapCutoff.Recipe.LocalOrdinaryInput.started_source_control_s2_oai.{u_1, u_2, u_3} := @OAI.SKGapCutoff.Recipe.LocalOrdinaryInput.started_source_control_s2_oai.{u_1, u_2, u_3}
