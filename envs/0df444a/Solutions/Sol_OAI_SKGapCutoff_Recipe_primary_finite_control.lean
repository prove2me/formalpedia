-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.primary_finite_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:11:42.733217+00:00
-- url     : https://prove2.me/submissions/d92c00a6-5f46-4e07-9507-f02d5db2a92e

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_OrdinaryData_ordinary_local_closure

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Spin
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

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_GibbsExpectation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

lemma flip_sub {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    f (flip x i) - f x = -2 * spin x i * halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [flip, hi, Bool.not_false, spin, Bool.false_eq_true, ↓reduceIte, halfDiff]
    rw [hx]; ring
  · simp only [flip, hi, Bool.not_true, spin, ↓reduceIte, halfDiff]
    rw [hx]; ring

end SKGapCutoff

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SquaredGaussianFourth
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
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

lemma scalarVariance_pos (y : ℝ) : 0 < scalarVariance y :=
  sub_pos.mpr (Real.tanh_sq_lt_one y)

lemma scalarVariance_le_one (y : ℝ) : scalarVariance y ≤ 1 := by
  unfold scalarVariance
  nlinarith [sq_nonneg (Real.tanh y)]

lemma scalarVariance_eq (y : ℝ) : scalarVariance y = 1 / Real.cosh y ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq y
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_hasDerivAt (y : ℝ) : HasDerivAt Real.tanh (scalarVariance y) y := by
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  convert! h using 1
  · ext z; exact Real.tanh_eq_sinh_div_cosh z
  · rw [scalarVariance_eq]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq y]

lemma tanh_lipschitz (x y : ℝ) : |Real.tanh y - Real.tanh x| ≤ |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (tanh_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => (show ‖scalarVariance z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_pos (scalarVariance_pos z)]
      exact scalarVariance_le_one z)) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [one_mul, Real.norm_eq_abs] using h

lemma scalarVariance_lipschitz (x y : ℝ) : |scalarVariance y - scalarVariance x| ≤ 2*|y-x| := by
  have h1 := tanh_lipschitz x y
  have h2 : |Real.tanh y + Real.tanh x| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_tanh_lt_one x, Real.abs_tanh_lt_one y])
  have he : scalarVariance y - scalarVariance x =
      -(Real.tanh y - Real.tanh x) * (Real.tanh y + Real.tanh x) := by
    unfold scalarVariance
    ring
  rw [he, abs_mul, abs_neg]
  nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)]

lemma tanh_linear_remainder (x y : ℝ) :
    |Real.tanh y - Real.tanh x - scalarVariance x * (y-x)| ≤ 2 * |y-x| ^ 2 := by
  let f (z : ℝ) := Real.tanh z - Real.tanh x - scalarVariance x * (z-x)
  have hd (z : ℝ) : HasDerivAt f (scalarVariance z - scalarVariance x) z := by
    convert! ((tanh_hasDerivAt z).sub_const (Real.tanh x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (scalarVariance x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_one]
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) : ‖scalarVariance z - scalarVariance x‖ ≤
      2 * |y-x| := by
    have hh : |z-x| ≤ |y-x| := by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    simpa only [Real.norm_eq_abs] using (scalarVariance_lipschitz x z).trans
      (mul_le_mul_of_nonneg_left hh (by norm_num))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x y) => (hd z).hasDerivWithinAt) hb
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using h

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_Taylor
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientFlip
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_PreparationGrowth
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
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
namespace SKGapCutoff

lemma refreshField_flip {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    H (flip x i) j = H x j - 2*spin x i*halfDiff i (fun y => H y j) x := by
  have h := flip_sub i (fun y => H y j) x
  linarith

lemma refreshField_abs_change {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |H x j-H (flip x i) j| = 2*|halfDiff i (fun y => H y j) x| := by
  rw [refreshField_flip H x i j]
  ring_nf
  simp [abs_mul, abs_spin_eq_one, mul_comm]

lemma refreshInfluence_error_le {n : ℕ} (H : VectorFields n) (x : Spin n) (i j : Fin n) :
    |refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j)| ≤
        4*(halfDiff i (fun y => H y j) x)^2 := by
  have hr := tanh_linear_remainder (H x j) (H (flip x i) j)
  have he : refreshInfluence (fun y k => Real.tanh (H y k)) x i j -
      halfDiff i (fun y => H y j) x*scalarVariance (H x j) =
      -(spin x i/2)*(Real.tanh (H (flip x i) j)-Real.tanh (H x j)-
        scalarVariance (H x j)*(H (flip x i) j-H x j)) := by
    simp only [refreshInfluence, halfDiff_as_flip]
    ring
  rw [he, abs_mul, abs_neg, abs_div, abs_spin_eq_one]
  norm_num only [abs_of_pos (show (0:ℝ)<2 by norm_num)]
  have ha : |H (flip x i) j-H x j| = 2*|halfDiff i (fun y => H y j) x| := by
    rw [abs_sub_comm, refreshField_abs_change]
  rw [ha] at hr
  nlinarith [sq_abs (halfDiff i (fun y => H y j) x)]

open RandomMatrix

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
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

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
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

lemma diagonalSeminorm_le (M : Matrix ι ι ℝ) : diagonalSeminorm M≤‖M‖ := by
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
  rw [diagonalSeminorm_sq,frobenius_sq]
  exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (M i k)) (Finset.mem_univ i))

lemma offDiagonalSeminorm_le (M : Matrix ι ι ℝ) : offDiagonalSeminorm M≤‖M‖ := by
  let a : ι×ι→ℝ := fun p=>if p.1=p.2 then 0 else (M p.1 p.2)^2
  have ha : ∀ p,0≤a p := by intro p;dsimp [a];split_ifs <;> positivity
  have hs : (∑ p,a p)≤‖M‖^2 := by
    rw [frobenius_sq]
    rw [show (∑ i,∑ k,(M i k)^2) = ∑ p : ι×ι,(M p.1 p.2)^2 from (Fintype.sum_prod_type fun p : ι×ι=>(M p.1 p.2)^2).symm]
    apply Finset.sum_le_sum
    intro p _
    dsimp [a]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
  rw [offDiagonalSeminorm_fourth]
  calc
    _ = ∑ p,a p^2 := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [a]
      split_ifs <;> ring
    _ ≤ (∑ p,a p)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun p _=>ha p)
    _ ≤ (‖M‖^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun p _=>ha p)) hs 2
    _ = ‖M‖^4 := by ring

omit [DecidableEq ι] in
lemma diagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    diagonalSeminorm (M+N)≤diagonalSeminorm M+diagonalSeminorm N := by
  simpa only [diagonalSeminorm,diagonalVector_add] using norm_add_le (diagonalVector M) (diagonalVector N)
lemma offDiagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    offDiagonalSeminorm (M+N)≤offDiagonalSeminorm M+offDiagonalSeminorm N := by
  simpa only [offDiagonalSeminorm,offDiagonalVector_add] using norm_add_le (offDiagonalVector M) (offDiagonalVector N)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormDiagonal
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

end SKGap

end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
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

lemma opNorm_add (M N : Interaction n) : SKGap.opNorm (M+N) ≤ SKGap.opNorm M+SKGap.opNorm N := by
  simp only [opNorm_eq,map_add]
  exact norm_add_le _ _

lemma opNorm_smul (c : ℝ) (M : Interaction n) : SKGap.opNorm (c • M) = |c| * SKGap.opNorm M := by
  simp only [opNorm_eq,map_smul,norm_smul,Real.norm_eq_abs]

lemma ShapeBound.mono {M : Interaction n} {C D : ℝ} (h : ShapeBound M C) (hCD : C≤D) :
    ShapeBound M D := ⟨h.1.trans hCD,h.2.1.trans hCD,h.2.2.trans hCD⟩

lemma ShapeBound.add {M N : Interaction n} {C D : ℝ}
    (hM : ShapeBound M C) (hN : ShapeBound N D) : ShapeBound (M+N) (C+D) := by
  exact ⟨(opNorm_add M N).trans (add_le_add hM.1 hN.1),
    (SKGap.diagonalSeminorm_add M N).trans (add_le_add hM.2.1 hN.2.1),
    (SKGap.offDiagonalSeminorm_add M N).trans (add_le_add hM.2.2 hN.2.2)⟩

lemma shapeBound_of_frobenius {M : Interaction n} {C : ℝ} (h : ‖M‖≤C) : ShapeBound M C :=
  ⟨(opNorm_le_frobenius M).trans h,(SKGap.diagonalSeminorm_le M).trans h,
    (SKGap.offDiagonalSeminorm_le M).trans h⟩

lemma ShapeBound.perturb {M H : Interaction n} {C E : ℝ}
    (hH : ShapeBound H C) (hE : ‖M-H‖≤E) : ShapeBound M (C+E) := by
  simpa only [add_sub_cancel] using hH.add (shapeBound_of_frobenius hE)

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

lemma quadratic_entry_error {D R : Interaction n} {C A : ℝ} (hC : 0≤C) (hA : 0≤A)
    (hD : ShapeBound D C) (he : ∀ i k, |R i k|≤A*(D i k)^2) :
    ‖R‖ ≤ 2*A*C^2 := by
  have hs : ‖R‖^2 ≤ A^2*(2*C^4) := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑ i,∑ k,A^2*(D i k)^4 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        have h := pow_le_pow_left₀ (abs_nonneg (R i k)) (he i k) 2
        nlinarith only [h,sq_abs (R i k)]
      _ = A^2*(∑ i,∑ k,(D i k)^4) := by simp_rw [← Finset.mul_sum]
      _ ≤ A^2*(2*C^4) := mul_le_mul_of_nonneg_left (fourth_sum_le hC hD) (sq_nonneg _)
  have hp : 0≤2*A*C^2 := by positivity
  nlinarith [sq_nonneg (A*C^2)]

lemma diagonal_mul_shape {M : Interaction n} {C : ℝ} {a : Fin n→ℝ}
    (ha : ∀ i,|a i|≤1) (hM : ShapeBound M C) :
    ShapeBound (Matrix.diagonal a*M) C := by
  have haN : SKGap.opNorm (Matrix.diagonal a)≤1 := SKGap.opNorm_diagonal_le (by norm_num) ha
  refine ⟨(SKGap.opNorm_mul _ _).trans ?_,?_,?_⟩
  · calc
      _ ≤ 1*SKGap.opNorm M := mul_le_mul_of_nonneg_right haN (norm_nonneg _)
      _ = SKGap.opNorm M := one_mul _
      _ ≤ C := hM.1
  · apply le_trans ?_ hM.2.1
    apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
    change SKGap.diagonalSeminorm _ ^2 ≤ SKGap.diagonalSeminorm M ^2
    simp only [SKGap.diagonalSeminorm_sq,Matrix.diagonal_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2
    simp only [sq_abs,one_pow] at hi
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hi (sq_nonneg (M i i))
  · apply le_trans ?_ hM.2.2
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
    change SKGap.offDiagonalSeminorm _ ^4 ≤ SKGap.offDiagonalSeminorm M ^4
    simp only [SKGap.offDiagonalSeminorm_fourth]
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact le_rfl
    · simp only [Matrix.diagonal_mul,mul_pow]
      have hi := pow_le_pow_left₀ (abs_nonneg (a p.1)) (ha p.1) 4
      rw [← abs_pow,abs_of_nonneg (by positivity : 0≤a p.1^4)] at hi
      simpa only [one_pow,one_mul] using mul_le_mul_of_nonneg_right hi
        (by positivity : 0≤(M p.1 p.2)^4)

lemma tanh_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*derivativeMatrix F x‖ ≤ 8*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤4) hD ?_ using 1 <;> try norm_num
  intro i k
  simpa only [derivativeMatrix,Matrix.sub_apply,Matrix.diagonal_mul,mul_comm,
    refreshInfluence] using refreshInfluence_error_le F x k i

lemma tanh_derivative_shape {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ShapeBound (derivativeMatrix (fun y i => Real.tanh (F y i)) x) (C+8*C^2) := by
  apply ShapeBound.perturb _ (tanh_derivative_error hC hD)
  apply diagonal_mul_shape ?_ hD
  intro i
  rw [abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

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

lemma derivativeMatrix_sub (F G : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => F y i-G y i) x=derivativeMatrix F x-derivativeMatrix G x := by
  ext i k
  exact halfDiff_sub k (fun y => F y i) (fun y => G y i) x

lemma derivativeMatrix_smul (c : ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => c*F y i) x=c • derivativeMatrix F x := by
  ext i k
  simp only [derivativeMatrix,halfDiff,Matrix.smul_apply,smul_eq_mul]
  ring

lemma derivativeMatrix_spin (x : Spin n) : derivativeMatrix spin x=1 := by
  ext i k
  simp [derivativeMatrix,Matrix.one_apply,eq_comm]

lemma variance_derivative_error {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C) :
    ‖derivativeMatrix (fun y i => 1-(F y i)^2) x-
      (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)‖ ≤ 4*C^2 := by
  convert quadratic_entry_error hC (by norm_num : (0:ℝ)≤2) hD ?_ using 1 <;> try norm_num
  intro i k
  have hs : halfDiff k (fun y => 1-(F y i)^2) x =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 := by
    have hh := halfDiff_mul k (fun y => F y i) (fun y => F y i) x
    rw [halfDiff_sub,halfDiff_const]
    simpa only [pow_two,zero_sub] using (show -(halfDiff k (fun y => F y i*F y i) x) =
      -2*F x i*halfDiff k (fun y => F y i) x+
        2*spin x k*(halfDiff k (fun y => F y i) x)^2 by rw [hh]; ring)
  simp only [derivativeMatrix,hs]
  have he (a b c : ℝ) : -2*a*b+2*c*b^2+2*(a*b)=2*c*b^2 := by ring
  rw [he,abs_mul,abs_mul,abs_spin_eq_one,mul_one]
  norm_num [abs_of_nonneg (sq_nonneg (halfDiff k (fun y => F y i) x))]

lemma variance_derivative_opNorm {F : VectorFields n} {x : Spin n} {C : ℝ}
    (hC : 0≤C) (hF : ∀ i,|F x i|≤1) (hD : ShapeBound (derivativeMatrix F x) C) :
    SKGap.opNorm (derivativeMatrix (fun y i => 1-(F y i)^2) x) ≤ 2*C+4*C^2 := by
  let A := (-2:ℝ) • (Matrix.diagonal (F x)*derivativeMatrix F x)
  have hA : SKGap.opNorm A≤2*C := by
    dsimp only [A]
    rw [opNorm_smul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (diagonal_mul_shape hF hD).1 (by norm_num)
  have hE := (opNorm_le_frobenius
    (derivativeMatrix (fun y i => 1-(F y i)^2) x-A)).trans (variance_derivative_error hC hD)
  have he : derivativeMatrix (fun y i => 1-(F y i)^2) x =
      A+(derivativeMatrix (fun y i => 1-(F y i)^2) x-A) := by abel
  rw [he]
  exact (opNorm_add _ _).trans (add_le_add hA hE)

lemma tanh_derivative_formal_error {F : VectorFields n} {x : Spin n}
    {H : Interaction n} {C E : ℝ} (hC : 0≤C) (hD : ShapeBound (derivativeMatrix F x) C)
    (hE : ‖derivativeMatrix F x-H‖≤E) :
    ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-
      Matrix.diagonal (fun i => scalarVariance (F x i))*H‖ ≤ 8*C^2+E := by
  let V := Matrix.diagonal (fun i => scalarVariance (F x i))
  have hV : SKGap.opNorm V≤1 := by
    apply SKGap.opNorm_diagonal_le (by norm_num)
    intro i
    rw [abs_of_pos (scalarVariance_pos _)]
    exact scalarVariance_le_one _
  have he : derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H =
      (derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*derivativeMatrix F x)+
        V*(derivativeMatrix F x-H) := by noncomm_ring
  change ‖derivativeMatrix (fun y i => Real.tanh (F y i)) x-V*H‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (tanh_derivative_error hC hD)
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg _)).trans (by simpa using hE))

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalCoefficient
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

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

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

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Error
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

local instance instFactLeENNRealOfNat_solutions_refdca5_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

end SKGap.SourceError

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Trace
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

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma SegmentRegular.mono {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C D : ℝ} (h : SegmentRegular H θ F F' x C) (hCD : C≤D) :
    SegmentRegular H θ F F' x D :=
  ⟨h.nonneg.trans hCD,h.deriv,(fun i k t ht=>(h.bound i k t ht).trans hCD),
    (fun i k t ht=>(h.lip i k t ht).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _)))⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

omit [DecidableEq ι]

lemma mean_abs_le_one [Nonempty ι] {a : ι→ℝ} (ha : ∀ i,|a i|≤1) :
    |Diagram.mean a|≤1 := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    |Diagram.mean a| = |∑ i,a i|/(Fintype.card ι:ℝ) := by
      rw [Diagram.mean,abs_div,abs_of_pos hn]
    _ ≤ (∑ i,|a i|)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ 1 := by
      rw [div_le_one hn]
      simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ha i)

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryDifferentiation
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

lemma primaryDiagonal_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ∀ k i, |primaryDiagonal j J h x k i|≤1 := by
  intro k i
  rw [primaryDiagonal,abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

lemma primaryState_mag_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (x : Spin n) (i : Fin n) : |(primaryState j J h k).1 x i|≤1 := by
  cases k with
  | zero => simp [primaryState,abs_spin_eq_one]
  | succ k => exact (Real.abs_tanh_lt_one _).le

lemma formalMag_previous (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalMag j J h x k =
      Matrix.diagonal (SKGap.Noncrossing.Primary.previousDiagonal (primaryDiagonal j J h x) k)*
        SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) k := by
  cases k <;> simp [formalMag,formalField,SKGap.Noncrossing.Primary.previousDiagonal,
    SKGap.Noncrossing.Primary.primaryMatrix]

lemma formalField_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    formalField j J h x (k+1) = J*formalMag j J h x (k+1)-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k := by
  change SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+2) =
    J*(Matrix.diagonal (primaryDiagonal j J h x k)*
      SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1))-
      (j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)) • formalMag j J h x k
  rw [formalMag_previous,SKGap.Noncrossing.Primary.primaryMatrix,Matrix.mul_assoc]

lemma onsager_derivative_error {F G : VectorFields n} {x : Spin n} {H P : Interaction n}
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) {C R : ℝ} (hn : 0<n)
    (hC : 0≤C) (hR : 0≤R) (hJ : SKGap.opNorm J≤R)
    (hF : ShapeBound (derivativeMatrix F x) C) (hFE : ‖derivativeMatrix F x-H‖≤C)
    (hGE : ‖derivativeMatrix G x-P‖≤C) (hG : SKGap.opNorm (derivativeMatrix G x)≤C)
    (hGb : ∀ i,|G x i|≤1) :
    let m : VectorFields n := fun y i => Real.tanh (F y i)
    let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖ ≤
      R*T+|j| *(C+Q+2*C*Q) := by
  let m : VectorFields n := fun y i => Real.tanh (F y i)
  let b : Spin n→ℝ := siteMean (fun y i => 1-(m y i)^2)
  let T := C+8*C^2
  let Q := 2*T+4*T^2
  change ‖derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x-
    (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P)‖≤_
  have hT : 0≤T := by dsimp [T]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hm : ShapeBound (derivativeMatrix m x) T := tanh_derivative_shape hC hF
  have hmE : ‖derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H‖≤T := by
    convert tanh_derivative_formal_error hC hF hFE using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [T]
    ring
  have hbQ : (n:ℝ)*‖derivativeVector b x‖^2≤Q^2 :=
    siteMean_derivative_square_bound hn (variance_derivative_opNorm hT
      (fun i => (Real.abs_tanh_lt_one _).le) hm)
  have hp : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x‖≤Q+2*C*Q :=
    product_derivative_error hn hQ hG hGb hbQ
  have hb : |b x|≤1 := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hv (i : Fin n) : |1-(m x i)^2|≤1 := by
      change |scalarVariance (F x i)|≤1
      rw [abs_of_pos (scalarVariance_pos _)]
      exact scalarVariance_le_one _
    simpa only [b,siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using
      SKGap.Noncrossing.Primary.mean_abs_le_one hv
  have hpE : ‖derivativeMatrix (fun y i => b y*G y i) x-b x • P‖≤C+Q+2*C*Q := by
    have he : derivativeMatrix (fun y i => b y*G y i) x-b x • P =
        (derivativeMatrix (fun y i => b y*G y i) x-b x • derivativeMatrix G x)+
          b x • (derivativeMatrix G x-P) := by module
    rw [he]
    apply (norm_add_le _ _).trans
    have hs : ‖b x • (derivativeMatrix G x-P)‖≤C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa using hGE)
    have hh := add_le_add hp hs
    linarith
  have hd : derivativeMatrix (fun y i => h i+∑ a,J i a*m y a-j*b y*G y i) x =
      J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x := by
    rw [derivativeMatrix_sub,derivativeMatrix_linear]
    congr 1
    convert derivativeMatrix_smul j (fun y i => b y*G y i) x using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext y i
    ring
  rw [hd]
  have he : J*derivativeMatrix m x-j • derivativeMatrix (fun y i => b y*G y i) x-
      (J*(Matrix.diagonal (fun i => scalarVariance (F x i))*H)-(j*b x) • P) =
      J*(derivativeMatrix m x-Matrix.diagonal (fun i => scalarVariance (F x i))*H)-
        j • (derivativeMatrix (fun y i => b y*G y i) x-b x • P) := by
    simp only [mul_sub,smul_sub,mul_smul]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul hJ hmE (norm_nonneg _) hR)
  · rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hpE (abs_nonneg _)

theorem primary_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    ‖derivativeMatrix (primaryState j J h k).2 x-formalField j J h x k‖≤C ∧
    ‖derivativeMatrix (primaryState j J h k).1 x-formalMag j J h x k‖≤C ∧
    SKGap.opNorm (derivativeMatrix (primaryState j J h k).1 x)≤C ∧
    ShapeBound (derivativeMatrix (primaryState j J h k).2 x) C := by
  induction k with
  | zero =>
    have hd : derivativeMatrix (primaryState j J h 0).2 x=J := by
      change derivativeMatrix (fun y i => h i+∑ a,J i a*spin y a) x=J
      rw [derivativeMatrix_linear,derivativeMatrix_spin,mul_one]
    have hm : derivativeMatrix (primaryState j J h 0).1 x=1 := derivativeMatrix_spin x
    have hf : formalField j J h x 0=J := rfl
    change _≤B+1 ∧ _≤B+1 ∧ _≤B+1 ∧ ShapeBound _ (B+1)
    rw [hd,hm,hf,formalMag,sub_self,norm_zero,sub_self,norm_zero]
    refine ⟨by positivity,by positivity,(SKGap.opNorm_one_le).trans ?_,?_⟩
    · linarith
    · exact (show ShapeBound J B by simpa only [hf] using hformal 0 le_rfl).mono (by linarith)
  | succ k ih =>
    obtain ⟨hFE,hGE,hG,hF⟩ := ih (fun l hl => hformal l (hl.trans (Nat.le_succ _)))
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    let E := R*T+|j| *(C+Q+2*C*Q)
    have hC : 0≤C := differentiationBound_nonneg hR hB k
    have hT : 0≤T := by dsimp [T]; positivity
    have hQ : 0≤Q := by dsimp [Q]; positivity
    have hE : 0≤E := by dsimp [E]; positivity
    have hnext : differentiationBound j R B (k+1)=B+1+E+T := rfl
    have hFE' : ‖derivativeMatrix (primaryState j J h (k+1)).2 x-formalField j J h x (k+1)‖≤E := by
      have hh := onsager_derivative_error (F := (primaryState j J h k).2)
        (G := (primaryState j J h k).1) j J h hn hC hR hJ hF hFE hGE hG
        (primaryState_mag_bounded j J h k x)
      have hb : siteMean (fun y i => 1-(Real.tanh ((primaryState j J h k).2 y i))^2) x =
          SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k) := by
        simp only [siteMean,SKGap.Noncrossing.Diagram.mean,primaryDiagonal,scalarVariance,Fintype.card_fin]
      dsimp only at hh
      rw [hb] at hh
      rw [formalField_succ]
      exact hh
    have hGE' : ‖derivativeMatrix (primaryState j J h (k+1)).1 x-formalMag j J h x (k+1)‖≤T := by
      have hh := tanh_derivative_formal_error hC hF hFE
      change ‖derivativeMatrix (fun y i => Real.tanh ((primaryState j J h k).2 y i)) x-
        Matrix.diagonal (fun i => scalarVariance ((primaryState j J h k).2 x i))*formalField j J h x k‖≤T
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [T]
      ring
    have hG' : SKGap.opNorm (derivativeMatrix (primaryState j J h (k+1)).1 x)≤T :=
      (tanh_derivative_shape hC hF).1
    have hF' : ShapeBound (derivativeMatrix (primaryState j J h (k+1)).2 x) (B+E) :=
      (hformal (k+1) le_rfl).perturb hFE'
    rw [hnext]
    exact ⟨hFE'.trans (by linarith),hGE'.trans (by linarith),hG'.trans (by linarith),
      hF'.mono (by linarith)⟩

theorem primary_average_differentiation {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ)
    (x : Spin n) (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀ l≤k, ShapeBound (formalField j J h x l) B) :
    let C := differentiationBound j R B k
    let T := C+8*C^2
    (n:ℝ)*‖derivativeVector (siteMean (fun y i =>
        scalarVariance ((primaryState j J h k).2 y i))) x‖^2≤(2*T+4*T^2)^2 := by
  have hC := differentiationBound_nonneg (j:=j) hR hB k
  have hF := (primary_differentiation J h x hn hR hB hJ k hformal).2.2.2
  apply siteMean_derivative_square_bound hn
  exact variance_derivative_opNorm (by positivity)
    (fun i => (Real.abs_tanh_lt_one _).le) (tanh_derivative_shape hC hF)

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix SKGap.Stein
variable {n : ℕ}

lemma mag_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) : mag j J h 0=spin := rfl
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientRow
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
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryRecipe
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

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma source_eq (a : ℕ) : D.source a=D.sourceOf a (fun b=>D.auxiliary b) := by
  rw [source,evaluate]; rfl
lemma auxiliary_eq (a : ℕ) : D.auxiliary a=D.fieldOf a (fun b=>D.source b) (fun b=>D.auxiliary b) := by
  rw [auxiliary,evaluate]; rfl

end OrdinaryData

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeCoefficientClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma SegmentValue.at {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ} {x : Spin n} {K : ℝ}
    (h : SegmentValue H θ F x K) (i : Fin n) : |coefficient H θ F x i|≤K := by
  simpa [coefficient] using h i i 0 (by constructor <;> norm_num)

omit [DecidableEq ι] [DecidableEq κ] in
lemma segmentRegular_const (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (c : ℝ) :
    SegmentRegular H θ (fun _ _=>c) (fun _ _=>0) x 0 := by
  refine ⟨le_rfl,fun _ _ _ _=>hasFDerivAt_const _ _,?_,?_⟩
  · intros; simp
  · intros; simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeBound
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

lemma recipeBudget_nonneg {c S : ℝ} (hc : 0 ≤ c) (hS : 0≤S) (a : ℕ) : 0 ≤ recipeBudget c S a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [recipeBudget]
    exact mul_nonneg hc (add_nonneg hS (Finset.sum_nonneg fun b _=>ih b b.isLt))

lemma recipeCost_nonneg {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    0 ≤ recipeCost A R L P j d := by unfold recipeCost; positivity

lemma recipeCost_ge {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    A+3*R ≤ recipeCost A R L P j d := by
  have hT : 0≤A+3*R := by positivity
  have hd : 0≤|j| *((d:ℝ)*(1+3*P)+1) := by positivity
  unfold recipeCost
  nlinarith [mul_nonneg hT hL,mul_nonneg hT hd]

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem evaluation_small (N : ℕ) (x : Spin n) (hn : 0<n) {A R L P S : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) (hS : 0≤S)
    (hJ : SKGap.opNorm D.J≤L) (hseed : (∑s,vectorNorm (D.seed s))≤S)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hs : ∀a≤N,∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀a≤N,∀b,CoefficientBound (D.auxCoefficient a b) x A R)
    (hsp : ∀a≤N,∀l s,CoefficientBound (D.seedPartial a l s) x A R)
    (hap : ∀a≤N,∀l b,CoefficientBound (D.auxPartial a l b) x A R) :
    ∀a≤N,
      SmallBound (D.source a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      SmallBound (D.auxiliary a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      ∀l,SmallBound (D.sourcePartial a l) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) := by
  let c:=recipeCost A R L P D.j (Fintype.card ι)
  have hc : 0 ≤ c := recipeCost_nonneg hA hR hL hP
  have hT : 0≤A+3*R := by positivity
  have hcg : A+3*R ≤ c := recipeCost_ge hA hR hL hP
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    let B : Fin a→ℝ := fun b=>recipeBudget c S b
    let I : ℝ := S+∑b,B b
    let Z : ℝ := I*(A+3*R)
    have hB : ∀b,0≤B b := fun b=>recipeBudget_nonneg hc hS b
    have hI : 0≤I := add_nonneg hS (Finset.sum_nonneg fun b _=>hB b)
    have hY : ∀b:Fin a,SmallBound (D.auxiliary b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).2.1
    have hW : ∀b:Fin a,SmallBound (D.source b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).1
    have hw : SmallBound (D.sourceOf a (fun b=>D.auxiliary b)) x Z :=
      (D.sourceOf_bound a _ x B hY (hs a haN) (ha a haN)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hp : ∀l,SmallBound (D.partialOf a l (fun b=>D.auxiliary b)) x Z := fun l=>
      (D.partialOf_bound a l _ x B hY (hsp a haN l) (hap a haN l)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hZ : Z ≤ recipeBudget c S a := by
      rw [recipeBudget]
      exact (mul_le_mul_of_nonneg_left hcg hI).trans_eq (by dsimp [I,B]; ring)
    have hf:=D.fieldOf_bound a (fun b=>D.source b) (fun b=>D.auxiliary b) x hn B hL hP hJ hw hp hW hm hdm (ha a haN)
    have hfC : (L*Z+|D.j| *((Fintype.card ι:ℝ)*(Z*(1+3*P))))+
          |D.j| *((∑b,B b)*(A+3*R)) ≤ recipeBudget c S a := by
      rw [recipeBudget]
      change _ ≤ c*I
      dsimp [c,recipeCost,Z,I]
      have h1 : 0≤(S+∑b,B b)*(A+3*R) := mul_nonneg hI hT
      have h2 : 0≤|D.j| *(S*(A+3*R)) := mul_nonneg (abs_nonneg _) (mul_nonneg hS hT)
      nlinarith only [h1,h2]
    refine ⟨?_,?_,?_⟩
    · rw [D.source_eq]; exact hw.mono hZ
    · rw [D.auxiliary_eq]; exact hf.mono hfC
    · intro l; exact (hp l).mono hZ

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SourceTree
variable {D : Type*}

lemma sourceMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    sourceMatrix j J (.leaf c)=c • 1 := by simp [sourceMatrix,words,matrixPolynomial,matrixWord]
lemma fieldMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    fieldMatrix j J (.leaf c)=c • J := by
  simp [fieldMatrix,words,matrixPolynomial,matrixWord,matrixLetter]
lemma sourceMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceMatrix j J (.branch p a b)=Matrix.diagonal p*fieldMatrix j J a+sourceMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixWord,matrixLetter]
lemma fieldMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldMatrix j J (.branch p a b)=J*(Matrix.diagonal p*fieldMatrix j J a)-
      (j*Diagram.mean p) • sourceMatrix j J a+fieldMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixPolynomial_scale,matrixWord,matrixLetter,mul_assoc,sub_eq_add_neg,add_assoc]
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma primaryTree_matrices (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    SourceTree.sourceMatrix j J (primaryTree j J h x k)=formalMag j J h x k ∧
    SourceTree.fieldMatrix j J (primaryTree j J h x k)=formalField j J h x k := by
  induction k with
  | zero => simp [primaryTree,SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,
      formalMag,formalField,primaryMatrix]
  | succ k ih =>
    constructor
    · simp [primaryTree,SourceTree.sourceMatrix_branch,SourceTree.sourceMatrix_leaf,ih.2,formalMag]
    · simp only [primaryTree,SourceTree.fieldMatrix_branch,SourceTree.fieldMatrix_leaf,zero_smul,
        add_zero,ih.1,ih.2]
      rw [formalField_succ,formalMag]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

lemma wordBounded_diag {A : ℝ} {w : OrdinaryWord n} (h : wordBounded A w)
    (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) : wordBounded A (w++[.diag p]) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact h l hl
  · have he : l=Letter.diag p := List.mem_singleton.mp hl; subst l; exact hp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

lemma mass_nonneg (P : WordPolynomial (ι:=Fin n)) : 0 ≤ mass P := by
  unfold mass
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr; exact abs_nonneg _)

end SKGap.Noncrossing.Primary.MarkedPolynomial

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryClosure
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

lemma small (a : ℕ) (ha : a≤N) :
    SmallBound (D.source a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    SmallBound (D.auxiliary a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    ∀l,SmallBound (D.sourcePartial a l) x (c.normBudget D.j (Fintype.card ι) a) :=
  D.evaluation_small N x h.dimension c.A_nonneg (c.row_nonneg _) c.L_nonneg c.P_nonneg c.S_nonneg
    h.interaction h.seed h.primaryValue h.primaryDerivative h.seed_bound h.aux_bound h.seed_partial_bound h.aux_partial_bound a ha

lemma mean_bound (a : ℕ) (ha : a≤N) (b : Fin a) : |siteMean (D.auxCoefficient a b) x| ≤ c.A :=
  coefficient_mean_value (D.auxCoefficient a b) x c.A_nonneg (h.auxValue a ha b)

end LocalOrdinaryInput

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientInputBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ] [Fintype τ]

theorem LocalOrdinaryInput.with_coefficients {D : OrdinaryData n ι κ σ} {N : ℕ}
    {T : ι→SourceTree (Fin n→ℝ)} {x : Spin n} {c : LocalConstants}
    (h : LocalOrdinaryInput D T x N c) (E : OrdinaryData n ι κ τ)
    (hJ : E.J=D.J) (hj : E.j=D.j) (hH : E.H=D.H) (hp : E.predecessor=D.predecessor) (hθ : E.θ=D.θ)
    (A : ℕ) (K S : ℝ) (hK : 1≤K) (hS : 0≤S)
    (hs : (∑s,vectorNorm (E.seed s))≤S) (hc : E.CoefficientClass A x K) :
    LocalOrdinaryInput E T x A (c.withCoefficient K S hK hS) := by
  refine ⟨h.dimension,?_,?_,?_,?_,?_,?_,hs,?_,hc.seedRegular,hc.auxRegular,?_,?_⟩
  · simpa only [hJ,LocalConstants.withCoefficient] using h.interaction
  · simpa only [hH,LocalConstants.withCoefficient] using h.primaryShape
  · simpa only [hH,hj,hJ,LocalConstants.withCoefficient] using h.primaryFieldError
  · simpa only [hp,hj,hJ,LocalConstants.withCoefficient] using h.primarySourceError
  · simpa only [hp] using h.primaryValue
  · simpa only [hp,LocalConstants.withCoefficient] using h.primaryDerivative
  · simpa only [hθ,LocalConstants.withCoefficient] using h.parameter
  · intro a ha s i; exact (hc.seedValue a ha s).at i
  · intro a ha b i; exact (hc.auxValue a ha b).at i

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

namespace OrdinaryData
lemma CoefficientClass.mono {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype σ] {D : OrdinaryData n ι κ σ} {N : ℕ} {x : Spin n}
    {K L : ℝ} (h : D.CoefficientClass N x K) (hKL : K≤L) : D.CoefficientClass N x L := by
  refine ⟨h.one_le.trans hKL,fun a ha s=>(h.seedRegular a ha s).mono hKL,
    fun a ha b=>(h.auxRegular a ha b).mono hKL,?_,?_⟩
  · intro a ha s i k t ht; exact (h.seedValue a ha s i k t ht).trans hKL
  · intro a ha b i k t ht; exact (h.auxValue a ha b i k t ht).trans hKL
end OrdinaryData

namespace FamilyRecipe
variable {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ} {N p : ℕ} {K : ℝ}

lemma sameEnvironment (H : FamilyRecipe j J h D N p K)
    {E : ∀a,OrdinaryData (n a) (Fin M) (Fin M) τ} {A r : ℕ} {L : ℝ}
    (H' : FamilyRecipe j J h E A r L) (a : Ω) :
    (D a).J=(E a).J ∧ (D a).j=(E a).j ∧ (D a).H=(E a).H ∧
      (D a).predecessor=(E a).predecessor ∧ (D a).θ=(E a).θ := by
  exact ⟨(H.interaction a).trans (H'.interaction a).symm,
    (H.coupling a).trans (H'.coupling a).symm,
    funext fun q=>(H.primary a q).trans (H'.primary a q).symm,
    funext fun q=>(H.predecessor a q).trans (H'.predecessor a q).symm,
    funext fun q=>(H.parameter a q).trans (H'.parameter a q).symm⟩

end FamilyRecipe
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma onsager_bounds (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤onsager j J h k x ∧ onsager j J h k x≤1 := by
  have hm (i : Fin n) : (mag j J h k x i)^2≤1 := by
    have H:=primaryState_mag_bounded j J h k x i
    have H':=sq_le_sq₀ (abs_nonneg (mag j J h k x i)) (by norm_num : (0:ℝ)≤1)
    simpa only [sq_abs,one_pow] using H'.mpr H
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hm i))) (Nat.cast_nonneg n)
  · by_cases hn : n=0
    · simp [onsager,siteMean,hn]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      calc
        (∑i:Fin n,(1-(mag j J h k x i)^2)) ≤ ∑i:Fin n,(1:ℝ) :=
          Finset.sum_le_sum fun i _=>sub_le_self _ (sq_nonneg _)
        _ = _ := by simp
lemma onsager_parameter_bound (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |j*(onsager j J h (k+1) x-onsager j J h k x)|≤|j| := by
  have H:=onsager_bounds j J h k x
  have H':=onsager_bounds j J h (k+1) x
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (show |onsager j J h (k+1) x-onsager j J h k x|≤1 from
    abs_le.mpr ⟨by linarith,by linarith⟩) (abs_nonneg j)
end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedDiagnostic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma wordBounded_append {A : ℝ} {u v : OrdinaryWord n}
    (hu : wordBounded A u) (hv : wordBounded A v) : wordBounded A (u++v) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact hu l hl
  · exact hv l hl

lemma MarkControl.mono {A : ℝ} {L K : ℕ} {t : SmallMark n} (h : MarkControl A L t) (hLK : L≤K) :
    MarkControl A K t := fun d hd=>⟨(h d hd).1,(h d hd).2.trans hLK⟩

lemma MarkControl.prepend {A : ℝ} {L : ℕ} {t : SmallMark n} (h : MarkControl A L t)
    (P : OrdinaryWord n) (hp : wordBounded A P) : MarkControl A (L+P.length) (t.prepend P) := by
  intro d hd
  rcases h d hd with ⟨hb,hl⟩
  cases t with
  | diagonal Q s R=>
    simp only [SmallMark.prepend,SmallMark.diagnostic,List.length_append,List.length_cons] at *
    constructor
    · intro l hh
      simp only [List.mem_append,List.mem_cons] at hh
      rcases hh with hh|hh|hh|hh
      · exact hb l (List.mem_append_left _ hh)
      · subst l; exact hb (.diag d) (by simp)
      · exact hp l hh
      · exact hb l (by simp [hh])
    · omega
  | average s Q=>
    simp only [SmallMark.prepend,SmallMark.diagnostic] at *
    exact ⟨wordBounded_append hp hb,by simp only [List.length_append]; omega⟩

lemma MarkedControl.append {A : ℝ} {L : ℕ} {P Q : MarkedPolynomial n}
    (hp : MarkedControl A L P) (hq : MarkedControl A L Q) : MarkedControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact hp t ht
  · exact hq t ht

lemma MarkedControl.mono {A : ℝ} {L K : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (hLK : L≤K) : MarkedControl A K P := fun t ht=>(h t ht).mono hLK

lemma MarkedControl.prepend {A : ℝ} {L : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (w : OrdinaryWord n) (hw : wordBounded A w) :
    MarkedControl A (L+w.length) (P.prepend w) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact (h s hs).prepend w hw

lemma MarkedControl.scale {A : ℝ} {L : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (c : ℝ) : MarkedControl A L (P.scale c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact h s hs

lemma diagonalWords_control {A : ℝ} {L : ℕ} (hA : 1≤A) (s : Fin n→ℝ)
    (P : WordPolynomial (ι:=Fin n)) (hP : ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L) :
    MarkedControl A (L+1) (diagonalWords s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  simp only [SmallMark.diagnostic,List.length_append,List.length_cons,List.length_nil]
  exact ⟨wordBounded_diag (hP r hr).1 d (fun i=>(hd i).trans hA),by have hh:=(hP r hr).2; omega⟩

lemma averageWords_control {A : ℝ} {L : ℕ} (c : ℝ) (s : Fin n→ℝ)
    (P : WordPolynomial (ι:=Fin n)) (hP : ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L) :
    MarkedControl A L (averageWords c s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact hP r hr

lemma zeroPair_control {A : ℝ} {L : ℕ} (hL : 1≤L) : PairControl (n:=n) A L zeroPair := by
  constructor
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd; exact ⟨by intro l hl; simp [SmallMark.diagnostic] at hl,by simp [SmallMark.diagnostic]⟩
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd
    constructor
    · intro l hl
      have he : l=Letter.noise := by simpa [SmallMark.diagnostic] using hl
      subst l
      trivial
    · simpa [SmallMark.diagnostic] using hL

lemma smallBranch_control {A : ℝ} {L K : ℕ} (hA : 1≤A) (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n)
    (hT : (∀t∈(T.words j).1,wordBounded A t.2 ∧ t.2.length≤L) ∧
      (∀t∈(T.words j).2,wordBounded A t.2 ∧ t.2.length≤L))
    (hV : PairControl A K V) : PairControl A K (smallBranch j p T V) := by
  have hd:=diagonalWords_control hA p _ hT.2
  have ha:=averageWords_control (-j) p _ hT.1
  have hn : wordBounded (n:=n) A [.noise] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
  refine ⟨(hd.mono (by omega)).append hV.1,?_⟩
  exact (((hd.prepend [.noise] hn).mono (by simp only [List.length_cons,List.length_nil]; omega)).append (ha.mono (by omega))).append hV.2

lemma boundedBranch_control {A : ℝ} {L K : ℕ} (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) (U V : Pair n)
    (hU : PairControl A L U) (hV : PairControl A K V) : PairControl A K (boundedBranch j p U V) := by
  have hd : wordBounded (n:=n) A [.diag p] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; exact hp
  have hd' : wordBounded (n:=n) A [.noise,.diag p] := by
    intro l hl; simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact hp
  refine ⟨((hU.2.prepend [.diag p] hd).mono (by simp only [List.length_singleton]; omega)).append hV.1,?_⟩
  exact (((hU.2.prepend [.noise,.diag p] hd').mono (by simp only [List.length_cons,List.length_nil]; omega)).append
    ((hU.1.scale _).mono (by omega))).append hV.2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
lemma PolynomialControl.mono {A : ℝ} {L K : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hLK : L≤K) : PolynomialControl A K P :=
  fun t ht=>⟨(h t ht).1,(h t ht).2.trans hLK⟩
lemma PolynomialControl.append {A : ℝ} {L : ℕ} {P Q : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (hQ : PolynomialControl A L Q) : PolynomialControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact h t ht
  · exact hQ t ht
lemma PolynomialControl.prepend {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (w : OrdinaryWord n) (hw : wordBounded A w) :
    PolynomialControl A (w.length+L) (prependWords w P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact ⟨wordBounded_append hw (h r hr).1,by simpa only [List.length_append] using Nat.add_le_add_left (h r hr).2 w.length⟩
lemma PolynomialControl.scale {A : ℝ} {L : ℕ} {P : WordPolynomial (ι:=Fin n)}
    (h : PolynomialControl A L P) (c : ℝ) : PolynomialControl A L (SKGap.Noncrossing.Primary.scale c P) := by
  intro t ht
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact h r hr
lemma polynomialControl_nil (c : ℝ) (A : ℝ) (L : ℕ) :
    PolynomialControl (n:=n) A L [(c,[])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  exact ⟨by intro l hl; simp at hl,Nat.zero_le _⟩
lemma polynomialControl_noise (c : ℝ) (A : ℝ) (L : ℕ) (hL : 1≤L) :
    PolynomialControl (n:=n) A L [(c,[.noise])] := by
  intro t ht
  have he:=List.mem_singleton.mp ht; subst t
  constructor
  · intro l hl
    have he:=List.mem_singleton.mp hl; subst l; trivial
  · exact hL
end SKGapCutoff.Recipe
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
theorem primaryTree_control (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ)
    {A : ℝ} (hA : 1≤A) :
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).1 ∧
    PolynomialControl A (2*k+1) ((primaryTree j J h x k).words j).2 := by
  induction k with
  | zero=>exact ⟨polynomialControl_nil _ _ _,polynomialControl_noise _ _ _ (by omega)⟩
  | succ k ih=>
    have hd : wordBounded A [.diag (primaryDiagonal j J h x k)] := by
      intro l hl
      have he:=List.mem_singleton.mp hl; subst l
      exact fun i=>(primaryDiagonal_bounded j J h x k i).trans hA
    have hv : PolynomialControl A (2*(k+1)+1) (prependWords [.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) :=
      (ih.2.prepend _ hd).mono (by simp only [List.length_singleton]; omega)
    have hn : wordBounded (n:=n) A [.noise] := by
      intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
    have hh : PolynomialControl A (2*(k+1)+1) (prependWords [.noise,.diag (primaryDiagonal j J h x k)]
        ((primaryTree j J h x k).words j).2) := by
      exact (ih.2.prepend _ (wordBounded_append hn hd)).mono (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
    simp only [primaryTree,SourceTree.words]
    exact ⟨hv.append (polynomialControl_nil _ _ _),
      (hh.append ((ih.1.scale _).mono (by omega))).append (polynomialControl_noise _ _ _ (by omega))⟩
end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeWordEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma pairControl_fold {τ : Type*} (xs : List τ) (f : τ→Pair n→Pair n) {A : ℝ} {L : ℕ}
    (hL : 1≤L) (hf : ∀t V,PairControl A L V→PairControl A L (f t V)) :
    PairControl A L (xs.foldr f zeroPair) := by
  induction xs with
  | nil=>exact zeroPair_control hL
  | cons t xs ih=>exact hf t _ ih

namespace OrdinaryData
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem markedRecipe_control (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N L : ℕ) {A : ℝ} (hA : 1≤A)
    (hT : ∀l,(∀t∈((T l).words D.j).1,wordBounded A t.2 ∧ t.2.length≤L) ∧
      (∀t∈((T l).words D.j).2,wordBounded A t.2 ∧ t.2.length≤L))
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A) :
    ∀a≤N,PairControl A (L+2*a+2) (D.markedRecipe T x a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih=>
    intro ha
    rw [markedRecipe]
    apply pairControl_fold _ _ (by omega)
    intro t V hV
    cases t with
    | inl l=>exact smallBranch_control hA (by omega) D.j _ _ _ (hT l) hV
    | inr b=>exact boundedBranch_control (by omega) D.j _ (hp a ha b) _ _ (ih b b.isLt (b.isLt.le.trans ha)) hV

end OrdinaryData

namespace OrdinaryData
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem ordinary_word_closure (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N L : ℕ) (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
    (hT : ∀l,(∀t∈((T l).words D.j).1,wordBounded c.A t.2 ∧ t.2.length≤L) ∧
      (∀t∈((T l).words D.j).2,wordBounded c.A t.2 ∧ t.2.length≤L))
    (hw : WordTestBound D.J c.A M (2*N+3))
    (hd : WordDiagramBound D.J D.j c.A B (L+2*N+2)) :
    let W:=c.normBudget D.j (Fintype.card ι)
    let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost D.j (Fintype.card ι))
    let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
    ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
      (∑i,|Primary.derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
      (∑i,|Primary.derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M := by
  apply D.ordinary_local_closure T x N c h hM hB hQ hm hw
  intro a ha d hdd
  have hc:=D.markedRecipe_control T x N L c.one_le_A hT h.auxValue a ha
  constructor
  · intro t ht
    have H:=(hc.1 t ht) d hdd
    exact hd _ (H.2.trans (by omega)) H.1
  · intro t ht
    have H:=(hc.2 t ht) d hdd
    exact hd _ (H.2.trans (by omega)) H.1

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_UniformOrdinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem uniform_ordinary_control (D : ∀a,OrdinaryData (n a) ι κ σ)
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ))
    (N L : ℕ) (c : LocalConstants) (j : ℝ) (hj : ∀a,(D a).j=j)
    (h : ∀a x,LocalOrdinaryInput (D a) (T a x) x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀a x l,mass ((T a x l).words j).1≤Q ∧ mass ((T a x l).words j).2≤Q)
    (hT : ∀a x l,PolynomialControl c.A L ((T a x l).words j).1 ∧
      PolynomialControl c.A L ((T a x l).words j).2)
    (hw : ∀a,WordTestBound (D a).J c.A M (2*N+3))
    (hd : ∀a,WordDiagramBound (D a).J j c.A B (L+2*N+2)) :
    ∃C : ℝ,0≤C ∧ ∀a x,
      SmallBound ((D a).source N) x C ∧
      (∀l,SmallBound ((D a).sourcePartial N l) x C) ∧
      (∑i,|derivativeMatrix ((D a).source N) x i i|)≤C := by
  let W:=c.normBudget j (Fintype.card ι)
  let R:=errorBudget (|j| *c.A) (c.sourceCost j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost j (Fintype.card ι))
  let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|j|)*Q)) (2+|j| *c.A) W
  let C:=|W N|+|V N*B+(R N).1*M|
  have hW : W N≤C := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hR : V N*B+(R N).1*M≤C := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨C,by dsimp [C]; positivity,fun a x=>?_⟩
  have hh:=(D a).ordinary_word_closure (T a x) x N L c (h a x) hM hB hQ
    (by simpa only [hj a] using hm a x) (by simpa only [hj a,PolynomialControl] using hT a x) (hw a)
    (by simpa only [hj a] using hd a) N le_rfl
  rw [hj a] at hh
  have hp:=(h a x).small N le_rfl
  rw [hj a] at hp
  exact ⟨hh.1.mono hW,fun l=>(hp.2.2 l).mono hW,hh.2.2.1.trans hR⟩

theorem uniform_auxiliary_mean (D : ∀a,OrdinaryData (n a) ι κ σ)
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ)) (N : ℕ) (c : LocalConstants)
    (h : ∀a x,LocalOrdinaryInput (D a) (T a x) x N c) (b : Fin N) :
    UniformMultiplier (fun a=>siteMean ((D a).auxCoefficient N b)) := by
  refine ⟨c.A,c.row (Fintype.card ι),c.A_nonneg,c.row_nonneg _,
    fun a x=>(h a x).mean_bound N le_rfl b,fun a x=>?_⟩
  have hm:=coefficient_mean_difference ((D a).auxCoefficient N b) x (c.row_nonneg _)
    ((h a x).aux_bound N le_rfl b).difference
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hm 2
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteRecipeControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

variable {M : ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

theorem finite_recipe_control (D₀ : ∀a,OrdinaryData (n a) (Fin M) (Fin M) Unit)
    (H₀ : FamilyRecipe j J h D₀ 0 0 1)
    (T : ∀a,Spin (n a)→Fin M→SourceTree (Fin (n a)→ℝ)) (c : LocalConstants)
    (hc : ∀a x,LocalOrdinaryInput (D₀ a) (T a x) x 0 c)
    (Nmax L : ℕ) (A W B Q : ℝ) (hA : 1≤A) (hW : 0≤W) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀a x q,mass ((T a x q).words j).1≤Q ∧ mass ((T a x q).words j).2≤Q)
    (hT : ∀a x q,PolynomialControl A L ((T a x q).words j).1 ∧
      PolynomialControl A L ((T a x q).words j).2)
    (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
    (hd : ∀a,WordDiagramBound (J a) j A B (L+2*Nmax+2)) :
    FiniteRecipeControl j J h M Nmax A := by
  have transfer {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
      (N p : ℕ) (K : ℝ) (H : FamilyRecipe j J h D N p K) (hKA : K≤A) :
      ∃c' : LocalConstants,c'.A=A ∧ ∀a x,LocalOrdinaryInput (D a) (T a x) x N c' := by
    obtain ⟨S,hS,hs⟩:=H.seed
    refine ⟨c.withCoefficient A S hA hS,rfl,fun a x=>?_⟩
    obtain ⟨hJ,hj,hH,hp,hθ⟩:=H.sameEnvironment H₀ a
    exact (hc a x).with_coefficients (D a) hJ hj hH hp hθ N A S hA hS (hs a)
      ((H.coefficients a x).mono hKA)
  constructor
  · intro σ inst D N p K H hN hKA
    obtain ⟨c',hAc,hi⟩:=transfer D N p K H hKA
    apply uniform_ordinary_control D T N L c' j H.coupling hi hW hB hQ hm
    · simpa only [hAc] using hT
    · intro a w hlen hb
      rw [H.interaction a,hAc] at *
      exact hw a w (hlen.trans (by omega)) hb
    · intro a w hlen hb
      rw [H.interaction a,hAc] at *
      exact hd a w (hlen.trans (by omega)) hb
  · intro σ inst D N p K H hN hKA b
    obtain ⟨c',hAc,hi⟩:=transfer D N p K H hKA
    exact uniform_auxiliary_mean D T N c' hi b
  · intro q
    refine ⟨|j|,c.V,abs_nonneg _,c.V_nonneg,
      fun a x=>onsager_parameter_bound j (J a) (h a) q.val x,fun a x=>?_⟩
    have hh : ‖derivativeVector ((D₀ a).θ q) x‖ ≤ c.V :=
      (Finset.single_le_sum (fun r _=>norm_nonneg (derivativeVector ((D₀ a).θ r) x))
        (Finset.mem_univ q)).trans (hc a x).parameter
    have hs:=pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [H₀.parameter a q,EuclideanSpace.real_norm_sq_eq] at hs
    exact hs

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

lemma emptyRecipe_coefficients (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M N : ℕ) (x : Spin n) :
    (emptyRecipe j J h M).CoefficientClass N x 1 := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩
  · intro a ha s; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [SegmentValue,emptyRecipe]
  · intros; norm_num [SegmentValue,emptyRecipe]

lemma emptyRecipe_family {Ω : Type*} {n : Ω→ℕ} (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M : ℕ) :
    FamilyRecipe j J h (fun a=>emptyRecipe j (J a) (h a) M) 0 0 1 := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
    ⟨0,le_rfl,?_⟩,fun a x=>emptyRecipe_coefficients j (J a) (h a) M 0 x,?_⟩
  · intro a; simp [emptyRecipe,vectorNorm]
  · intro a r hr q hq; omega

lemma emptyRecipe_local (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M : ℕ)
    (T : Fin M→SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)) (x : Spin n)
    {P L E V : ℝ} (hP : 0≤P) (hL : 0≤L) (hE : 0≤E) (hV : 0≤V) (hn : 0<n)
    (hJ : SKGap.opNorm J≤L)
    (hshape : ∀q:Fin M,ShapeBound (derivativeMatrix (fld j J h q.val) x) P)
    (hfield : ∀q:Fin M,‖derivativeMatrix (fld j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.fieldMatrix j J (T q)‖≤E)
    (hsource : ∀q:Fin M,‖derivativeMatrix (mag j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.sourceMatrix j J (T q)‖≤E)
    (hderiv : ∀q:Fin M,SKGap.opNorm (derivativeMatrix (mag j J h q.val) x)≤P)
    (hparam : (∑q:Fin M,‖derivativeVector (fun y=>j*(onsager j J h (q.val+1) y-onsager j J h q.val y)) x‖)≤V) :
    LocalOrdinaryInput (emptyRecipe j J h M) T x 0
      ⟨1,1,P,L,E,V,0,le_rfl,zero_le_one,le_rfl,hP,hL,hE,hV,le_rfl⟩ := by
  refine ⟨hn,hJ,hshape,hfield,hsource,?_,hderiv,?_,hparam,?_,?_,?_,?_⟩
  · intro q i; exact primaryState_mag_bounded j J h q.val x i
  · simp [emptyRecipe,vectorNorm]
  · intro a ha s; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [OrdinaryData.seedCoefficient,coefficient,emptyRecipe]
  · intros; norm_num [OrdinaryData.auxCoefficient,coefficient,emptyRecipe]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing.Primary
variable {n : ℕ}

lemma localPrimaryBudget_bounds {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) (q : Fin M) :
    differentiationBound j R B q.val≤localPrimaryBudget j R B M ∧
    averageBudget j R B q.val≤localPrimaryBudget j R B M := by
  have hh:=Finset.single_le_sum (s:=Finset.univ)
    (fun r (_:r∈Finset.univ)=>add_nonneg (differentiationBound_nonneg (j:=j) hR hB r.val)
      (averageBudget_nonneg (j:=j) hR hB r.val)) (Finset.mem_univ q)
  have h1:=differentiationBound_nonneg (j:=j) hR hB q.val
  have h2:=averageBudget_nonneg (j:=j) hR hB q.val
  exact ⟨(le_add_of_nonneg_right h2).trans hh,(le_add_of_nonneg_left h1).trans hh⟩

lemma onsager_derivative_bound {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) {q : ℕ} (hq : q≤M) :
    ‖derivativeVector (onsager j J h q) x‖≤localPrimaryBudget j R B M := by
  cases q with
  | zero=>
    have he : onsager j J h 0=0:=funext (onsager_zero j J h)
    rw [he]
    have hz : derivativeVector (0 : Spin n→ℝ) x=0 := by
      ext i; simp [derivativeVector,halfDiff]
    rw [hz,norm_zero]
    exact localPrimaryBudget_nonneg (j:=j) hR hB M
  | succ k=>
    have hh:=primary_average_differentiation J h x hn hR hB hJ k (fun l hl=>hformal l (by omega))
    have hh':(n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j R B k)^2 := by
      simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using hh
    exact (derivative_norm_of_mean_square hn (averageBudget_nonneg hR hB k) hh').trans
      (localPrimaryBudget_bounds hR hB M ⟨k,by omega⟩).2

lemma derivativeVector_mul_sub (c : ℝ) (f g : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*(f y-g y)) x=c • (derivativeVector f x-derivativeVector g x) := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,PiLp.sub_apply]
  simp only [halfDiff]
  ring

theorem primary_local_input {j R B : ℝ} (J : Interaction n) (h : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hR : 0≤R) (hB : 0≤B) (hJ : SKGap.opNorm J≤R) (M : ℕ)
    (hformal : ∀l<M,ShapeBound (formalField j J h x l) B) :
    let C:=localPrimaryBudget j R B M
    LocalOrdinaryInput (emptyRecipe j J h M) (fun q=>primaryTree j J h x q.val) x 0
      ⟨1,1,C,R,C,(M:ℝ)*(|j| *(C+C)),0,le_rfl,zero_le_one,le_rfl,
        localPrimaryBudget_nonneg hR hB M,hR,localPrimaryBudget_nonneg hR hB M,
        by positivity [localPrimaryBudget_nonneg (j:=j) hR hB M],le_rfl⟩ := by
  dsimp only
  have hC:=localPrimaryBudget_nonneg (j:=j) hR hB M
  have hb:=localPrimaryBudget_bounds (j:=j) hR hB M
  have hd (q : Fin M):=primary_differentiation J h x hn hR hB hJ q.val
    (fun l hl=>hformal l (by omega))
  apply emptyRecipe_local j J h M _ x hC hR hC _ hn hJ
  · intro q; exact (hd q).2.2.2.mono (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).2]
    exact (hd q).1.trans (hb q).1
  · intro q; rw [(primaryTree_matrices j J h x q.val).1]
    exact (hd q).2.1.trans (hb q).1
  · intro q; exact (hd q).2.2.1.trans (hb q).1
  · calc
      _ ≤ ∑q:Fin M,|j| *(localPrimaryBudget j R B M+localPrimaryBudget j R B M) := by
        apply Finset.sum_le_sum; intro q _
        rw [derivativeVector_mul_sub,norm_smul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (norm_sub_le _ _).trans (add_le_add
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega))
          (onsager_derivative_bound J h x hn hR hB hJ M hformal (by omega)))
      _ = _ := by simp

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipePrimaryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma mass_append (P Q : WordPolynomial (ι:=Fin n)) : mass (P++Q)=mass P+mass Q := by
  simp [mass]
lemma mass_prefix (F : List (Letter (Fin n→ℝ))) (P : WordPolynomial (ι:=Fin n)) :
    mass (prependWords F P)=mass P := by simp [mass,prependWords,List.map_map,Function.comp_def]
lemma mass_scale (c : ℝ) (P : WordPolynomial (ι:=Fin n)) : mass (Primary.scale c P)=|c| *mass P := by
  induction P with
  | nil => simp [mass,Primary.scale]
  | cons t P ih =>
    simp only [Primary.scale,List.map_cons,mass,List.sum_cons,abs_mul] at *
    rw [ih]; ring
end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary MarkedPolynomial
variable {n : ℕ}

lemma primaryTree_mass (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    mass ((primaryTree j J h x k).words j).1≤(2+|j|)^k ∧
    mass ((primaryTree j J h x k).words j).2≤(2+|j|)^k := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  induction k with
  | zero => simp [primaryTree,SourceTree.words,mass]
  | succ k ih =>
    have hm := mean_abs_le_one (primaryDiagonal_bounded j J h x k)
    have hc : 0≤(2+|j|)^k := by positivity
    have hj : 0≤|j| := abs_nonneg _
    have ht : |j*SKGap.Noncrossing.Diagram.mean (primaryDiagonal j J h x k)|≤|j| := by
      rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left hm hj
    simp only [primaryTree,SourceTree.words,mass_append,mass_prefix,mass_scale]
    have hz₁ : mass ([(0,[])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    have hz₂ : mass ([(0,[.noise])] : WordPolynomial (ι:=Fin n))=0 := by simp [mass]
    simp only [hz₁,hz₂,add_zero,abs_neg]
    constructor
    · rw [pow_succ]; nlinarith [ih.2,mul_nonneg hj hc]
    · have ht' := mul_le_mul ht ih.1 (mass_nonneg _) hj
      rw [pow_succ]
      nlinarith [ih.2]

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryFiniteControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem primary_finite_control_oai (j R B : ℝ) (hR : 0≤R) (hB : 0≤B)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M Nmax : ℕ)
    (hn : ∀a,0<n a) (hJ : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M → ShapeBound (formalField j (J a) (h a) x l) B)
    (A W D : ℝ) (hA : 1≤A) (hW : 0≤W) (hD : 0≤D)
    (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
    (hd : ∀a,WordDiagramBound (J a) j A D ((2*M+1)+2*Nmax+2)) :
    FiniteRecipeControl j J h M Nmax A := by
  let C:=localPrimaryBudget j R B M
  have hC:=localPrimaryBudget_nonneg (j:=j) hR hB M
  let c : LocalConstants:=
    ⟨1,1,C,R,C,(M:ℝ)*(|j| *(C+C)),0,le_rfl,zero_le_one,le_rfl,
      hC,hR,hC,by dsimp [C]; positivity [localPrimaryBudget_nonneg (j:=j) hR hB M],le_rfl⟩
  apply finite_recipe_control (fun a=>emptyRecipe j (J a) (h a) M)
    (emptyRecipe_family j J h M) (fun a x q=>primaryTree j (J a) (h a) x q.val)
    c (fun a x=>primary_local_input (J a) (h a) x (hn a) hR hB (hJ a) M (hformal a x))
    Nmax (2*M+1) A W D ((2+|j|)^M) hA hW hD (by positivity)
  · intro a x q
    have hm:=primaryTree_mass (hn a) j (J a) (h a) x q.val
    have hp : (2+|j|)^q.val≤(2+|j|)^M:=
      pow_le_pow_right₀ (by linarith [abs_nonneg j]) q.isLt.le
    exact ⟨hm.1.trans hp,hm.2.trans hp⟩
  · intro a x q
    have ht:=primaryTree_control j (J a) (h a) x q.val hA
    exact ⟨ht.1.mono (by omega),ht.2.mono (by omega)⟩
  · exact hw
  · exact hd

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.primary_finite_control_oai.{u} := @OAI.SKGapCutoff.Recipe.primary_finite_control_oai.{u}
