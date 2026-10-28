-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:14:31.506113+00:00
-- url     : https://prove2.me/submissions/d4953ed9-b7ec-43d1-84c0-3ee8f2982c56

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_primary_finite_control
import Theorems.Thm_OAI_SKGapCutoff_Recipe_uniform_ordinary_weak_residual_s2
import Theorems.Thm_OAI_SKGapCutoff_Recipe_uniform_residual_square_rule_s2

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

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_Character
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

lemma spin_replace_of_ne {n : ℕ} (x : Spin n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    spin (replace x i b) j = spin x j := by
  simp [spin, replace, Function.update_of_ne h]

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_GibbsExpectation
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

lemma spin_flip {n : ℕ} (x : Spin n) (i j : Fin n) :
    spin (flip x i) j = spin x j - if j = i then 2 * spin x i else 0 := by
  by_cases h : j = i
  · subst j; simp; ring
  · simp [flip, spin_replace_of_ne x h, h]

lemma energy_flip {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (hdiag : ∀ i, J i i = 0) (x : Spin n) (i : Fin n) :
    energy J (flip x i) = energy J x - 2 * spin x i * field J x i := by
  have hr : ∑ j, spin x j * J j i = field J x i := by
    simp only [field, hJ, mul_comm]
  unfold energy
  simp only [spin_flip, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, hdiag]
  simp only [← Finset.sum_mul, hr]
  simp only [mul_assoc, ← Finset.mul_sum, field]
  ring

lemma exp_two_mul_one_sub_tanh (a : ℝ) :
    Real.exp (2 * a) * (1 - Real.tanh a) = 1 + Real.tanh a := by
  rw [Real.tanh_eq, show 2 * a = a + a by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos a
  field_simp
  nlinarith

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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

namespace KernelExpr

lemma mass_nonneg (f : KernelExpr) : 0 ≤ mass f := by
  induction f <;> simp only [mass] <;> positivity

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiFrechet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

namespace KernelExpr
lemma dBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.dBudget R := by
  unfold dBudget
  exact mul_nonneg (add_nonneg (add_nonneg f.dz.mass_nonneg f.dr.mass_nonneg) f.da.mass_nonneg)
    (Real.exp_pos _).le
lemma ddBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.ddBudget R :=
  add_nonneg (add_nonneg (f.dz.dBudget_nonneg R) (f.dr.dBudget_nonneg R)) (f.da.dBudget_nonneg R)

end KernelExpr

end SKGap.Stein

end
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_BilinearCoefficient
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
namespace SKGapCutoff.RandomMatrix

lemma matrix_column_sq_le {n : ℕ} (J : Interaction n) (j : Fin n) :
    ∑ i, J i j^2 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖^2 := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hh : ‖A e‖ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  have hv : ‖A e‖^2 = ∑ i, J i j^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hi : A e i = J i j := by
      change (∑ k, J i k * ((Pi.single j (1:ℝ) : Fin n → ℝ) k)) = J i j
      simp [Pi.single_apply]
    rw [hi]
  rw [← hv]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

end SKGapCutoff.RandomMatrix

open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PreparationGrowth
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_OpNormDiagonal
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

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_PhiRegularity
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
-- module Solutions.OAIQ074_CM.SKGap_Matrix_PrimaryMatrix
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
-- module Solutions.OAIQ074_CM.SKGap_Localization_PrimaryDifferentiation
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

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ResidualInduction
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

end SKGapCutoff.Primary

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

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma source_eq (a : ℕ) : D.source a=D.sourceOf a (fun b=>D.auxiliary b) := by
  rw [source,evaluate]; rfl

end OrdinaryData

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_RecipeCoefficientClosure
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
-- module Solutions.OAIQ074_CM.SKGap_Gaussian_SteinRecipeRegularity
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
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma steinCoefficientBudget_nonneg (R : ℝ) : 0 ≤ steinCoefficientBudget R := by
  have h0:= (KernelExpr.atom 0 0 false).mass_nonneg
  have h1:= (KernelExpr.atom 0 0 false).dBudget_nonneg R
  have h2:= (KernelExpr.atom 0 0 false).ddBudget_nonneg R
  unfold steinCoefficientBudget
  positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ResidualMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma halfDiff_mul_flipped (i : Fin n) (θ G : Observables n) (x : Spin n) :
    halfDiff i (fun y=>θ y*G y) x=θ (flip x i)*halfDiff i G x+G x*halfDiff i θ x := by
  rw [halfDiff_mul]
  have h:=flip_sub i θ x
  rw [show θ (flip x i)=θ x-2*spin x i*halfDiff i θ x by linarith]
  ring

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

lemma UniformWeak.zero (P : ∀a,Observables (n a)) : UniformWeak P (fun _ _=>0) := by
  refine ⟨0,le_rfl,?_⟩
  simp

lemma UniformWeak.congr {P F F' : ∀a,Observables (n a)} (h : UniformWeak P F)
    (he : ∀a x,F a x=F' a x) : UniformWeak P F' := by
  have : F=F' := funext fun a=>funext (he a)
  rwa [←this]

lemma UniformWeak.add {P F H : ∀a,Observables (n a)} (hF : UniformWeak P F)
    (hH : UniformWeak P H) : UniformWeak P (fun a x=>F a x+H a x) := by
  obtain ⟨C,hC,hF⟩:=hF
  obtain ⟨D,hD,hH⟩:=hH
  refine ⟨C+D,add_nonneg hC hD,fun a G=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a G) (hH a G)).trans_eq (by ring))

lemma UniformMultiplier.const (c : ℝ) : UniformMultiplier (n:=n) (fun _ _=>c) := by
  refine ⟨|c|,0,abs_nonneg _,le_rfl,fun _ _=>le_rfl,?_⟩
  intro a x
  simp [halfDiff]

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_UniformRecipeClass
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

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.add {F H : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hH : UniformMultiplier H) : UniformMultiplier (fun a x=>F a x+H a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨C,K,hC,hK,hH,hdH⟩:=hH
  refine ⟨B+C,Real.sqrt (2*L^2+2*K^2),add_nonneg hB hC,Real.sqrt_nonneg _,
    fun a x=>(abs_add_le _ _).trans (add_le_add (hF a x) (hH a x)),fun a x=>?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have he (i : Fin (n a)) : halfDiff i (fun y=>F a y+H a y) x=halfDiff i (F a) x+halfDiff i (H a) x := by
    unfold halfDiff; ring
  simp only [he]
  calc
    _ ≤ ∑i,(2*(halfDiff i (F a) x)^2+2*(halfDiff i (H a) x)^2) := by
      apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (halfDiff i (F a) x-halfDiff i (H a) x)]
    _ = 2*(∑i,(halfDiff i (F a) x)^2)+2*(∑i,(halfDiff i (H a) x)^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by linarith [hdF a x,hdH a x]
end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_MarkedDiagnostic
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

lemma wordBounded_mono {A B : ℝ} {u : OrdinaryWord n} (h : wordBounded A u) (hab : A≤B) :
    wordBounded B u := by
  intro l hl; cases l with
  | noise=>trivial
  | diag p=>exact fun i=>(h (.diag p) hl i).trans hab

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_UniformResidual
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

lemma residualCoefficientBudget_antitone (j : ℝ) {K : ℝ} (hK : 0≤K) (t : ℕ) :
    Antitone (residualCoefficientBudget j K t) := by
  intro p q hpq
  apply mul_le_mul_of_nonneg_left _ hK
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) (Nat.sub_le_sub_left hpq t)
lemma residualCoefficientBudget_ge (j : ℝ) {K : ℝ} (hK : 0≤K) (t p : ℕ) :
    K ≤ residualCoefficientBudget j K t p := by
  simpa only [mul_one,residualCoefficientBudget] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ (by linarith [steinCoefficientBudget_nonneg |j|]) :
      1≤(1+4*steinCoefficientBudget |j|)^(t-p)) hK
lemma residualCoefficientBudget_step (j K : ℝ) {t k : ℕ} (hk : k<t) :
    residualCoefficientBudget j K t (k+1)+4*steinCoefficientBudget |j| *residualCoefficientBudget j K t (k+1)=
      residualCoefficientBudget j K t k := by
  have he : t-k=(t-(k+1))+1 := by omega
  dsimp only [residualCoefficientBudget]
  rw [he,pow_succ]
  ring

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

lemma UniformSquare.zero (P : ∀a,Observables (n a)) : UniformSquare P (fun _ _=>0) := by
  intro B L hB hL
  exact ⟨0,le_rfl,by simp⟩
lemma UniformSquare.congr {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (he : ∀a x,F a x=H a x) : UniformSquare P H := by
  have : F=H:=funext fun a=>funext (he a)
  rwa [←this]
lemma UniformSquare.add {P F H : ∀a,Observables (n a)} (hF : UniformSquare P F)
    (hH : UniformSquare P H) : UniformSquare P (fun a x=>F a x+H a x) := by
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF B L hB hL
  obtain ⟨D,hD,hH⟩:=hH B L hB hL
  refine ⟨C+D,add_nonneg hC hD,fun a f θ ht hd=>?_⟩
  simp only [mul_add,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans ((add_le_add (hF a f θ ht hd) (hH a f θ ht hd)).trans_eq (by ring))

lemma scalar_product_bounds {n : ℕ} (θ η : Observables n) {B L D K : ℝ}
    (hB : 0≤B) (_ : 0≤L) (_ : 0≤D) (_ : 0≤K)
    (ht : ∀x,|θ x|≤B) (hdt : ∀x,∑i,(halfDiff i θ x)^2≤L^2)
    (he : ∀x,|η x|≤D) (hde : ∀x,∑i,(halfDiff i η x)^2≤K^2) :
    (∀x,|θ x*η x|≤B*D) ∧
    (∀x,∑i,(halfDiff i (fun y=>θ y*η y) x)^2≤(Real.sqrt (2*B^2*K^2+2*D^2*L^2))^2) := by
  constructor
  · intro x; rw [abs_mul]; exact mul_le_mul (ht x) (he x) (abs_nonneg _) hB
  · intro x
    rw [Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ∑i,(2*B^2*(halfDiff i η x)^2+2*D^2*(halfDiff i θ x)^2) := by
        apply Finset.sum_le_sum; intro i _
        rw [halfDiff_mul_flipped]
        have h1 : (θ (flip x i))^2≤B^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ht (flip x i)) 2
        have h2 : (η x)^2≤D^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he x) 2
        have h1':=mul_le_mul_of_nonneg_right h1 (sq_nonneg (halfDiff i η x))
        have h2':=mul_le_mul_of_nonneg_right h2 (sq_nonneg (halfDiff i θ x))
        nlinarith only [h1',h2',sq_nonneg (θ (flip x i)*halfDiff i η x-η x*halfDiff i θ x)]
      _ = 2*B^2*(∑i,(halfDiff i η x)^2)+2*D^2*(∑i,(halfDiff i θ x)^2) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hde x) (by positivity))
        (mul_le_mul_of_nonneg_left (hdt x) (by positivity))

lemma UniformSquare.mul {P F η : ∀a,Observables (n a)} (_ : ∀a x,0≤P a x)
    (hF : UniformSquare P F) (hη : UniformMultiplier η) :
    UniformSquare P (fun a x=>η a x*F a x) := by
  obtain ⟨D,K,hD,hK,he,hde⟩:=hη
  intro B L hB hL
  obtain ⟨C,hC,hF⟩:=hF (B*D) (Real.sqrt (2*B^2*K^2+2*D^2*L^2))
    (mul_nonneg hB hD) (Real.sqrt_nonneg _)
  refine ⟨C,hC,fun a f θ ht hd=>?_⟩
  obtain ⟨h1,h2⟩:=scalar_product_bounds θ (η a) hB hL hD hK ht hd (he a) (hde a)
  convert hF a f (fun x=>θ x*η a x) h1 h2 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl; intro x _; ring

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_UniformSquareInduction
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_ordinary_square_residual (p N : ℕ) {K : ℝ} (hK : 2≤K) (hM : p<M)
    (C : FiniteRecipeControl j J h M (N+2*p) (residualCoefficientBudget j K p 0))
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformSquare P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hK0 : 0≤K := by linarith
  have hb:=residualCoefficientBudget_antitone j hK0 p
  have HH:=uniform_residual_square_rule_s2 C hP hp hm hn hJ (residualCoefficientBudget j K p) hb p hM
    (fun r _=>hb (Nat.zero_le r)) (fun r _=>hK.trans (residualCoefficientBudget_ge j hK0 p r))
    (fun k hk=>le_of_eq (residualCoefficientBudget_step j K hk)) p le_rfl D N
  apply HH _ le_rfl
  simpa [residualCoefficientBudget] using H

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_FieldGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

lemma fieldPartition_pos (J : Interaction n) (h : Fin n→ℝ) : 0<fieldPartition J h :=
  Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty
lemma fieldGibbs_pos (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : 0<fieldGibbs J h x :=
  div_pos (Real.exp_pos _) (fieldPartition_pos J h)
lemma sum_fieldGibbs (J : Interaction n) (h : Fin n→ℝ) : ∑x,fieldGibbs J h x=1 := by
  simp only [fieldGibbs,←Finset.sum_div]
  change fieldPartition J h/fieldPartition J h=1
  exact div_self (ne_of_gt (fieldPartition_pos J h))

lemma fieldEnergy_flip (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldEnergy J h (flip x i)=fieldEnergy J h x-2*spin x i*(h i+field J x i) := by
  simp only [fieldEnergy,energy_flip J hJ hd,spin_flip,mul_sub,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  ring

lemma fieldGibbs_detailed_balance (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    fieldGibbs J h (flip x i)*(1+spin x i*Real.tanh (h i+field J x i))=
      fieldGibbs J h x*(1-spin x i*Real.tanh (h i+field J x i)) := by
  simp only [fieldGibbs,fieldEnergy_flip J hJ hd,Real.exp_sub]
  cases hi:x i
  · simp only [spin,hi,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul,mul_neg,Real.exp_neg]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]
  · simp only [spin,hi,↓reduceIte,one_mul,mul_one]
    have ht:=exp_two_mul_one_sub_tanh (h i+field J x i)
    field_simp [ne_of_gt (fieldPartition_pos J h)]
    nlinarith only [ht]

namespace Static
lemma conditionalMean_fieldGibbs (J : Interaction n) (hJ : ∀i k,J i k=J k i)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Real.tanh (h i+field J x i) := by
  have hb:=fieldGibbs_detailed_balance J hJ hd h x i
  have hp:=ne_of_gt (add_pos (fieldGibbs_pos J h x) (fieldGibbs_pos J h (flip x i)))
  rw [conditionalMean,←mul_div_assoc]
  apply (div_eq_iff hp).2
  cases hi:x i <;> simp only [spin,hi,Bool.false_eq_true,↓reduceIte,one_mul,neg_mul] at hb ⊢ <;>
    linarith only [hb]

lemma conditionalMean_primary (j : ℝ) (J : Interaction n) (hJ : J.IsSymm)
    (hd : ∀i,J i i=0) (h : Fin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalMean (fieldGibbs J h) x i=Primary.mag j J h 1 x i := by
  rw [conditionalMean_fieldGibbs J (fun i k=>hJ.apply k i) hd]
  rfl
end Static
end SKGapCutoff

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {j R B W C K : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

theorem gibbs_ordinary_residuals (p N : ℕ) (hK : 2≤K) (hM : p<M)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j K p 0) B W C M (N+2*p) (J a))
    {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (H : FamilyRecipe j J h D N p K) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i) := by
  have hA : 1 ≤ residualCoefficientBudget j K p 0 :=
    (by linarith : 1≤K).trans (residualCoefficientBudget_ge j (by linarith) p 0)
  have hc:=primary_finite_control j R B hR hB J h M (N+2*p) hn
    (fun a=>(hevent a).1) (fun a x l hl=>(hevent a).2.1 (h a) x l hl)
    _ W C hA hW hC (fun a=>(hevent a).2.2.1) (fun a=>(hevent a).2.2.2)
  have hp : ∀a x,0≤fieldGibbs (J a) (h a) x:=fun a x=>(fieldGibbs_pos _ _ _).le
  have hm:=fun a=>conditionalMean_primary j (J a) (hJ a) (hdiag a) (h a)
  exact ⟨uniform_ordinary_weak_residual_s2 p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H,
    uniform_ordinary_square_residual p N hK hM hc hp (fun a=>sum_fieldGibbs _ _) hm hn hJ D H⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (vectorPair U V) x =
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix U x)ᵀ) (WithLp.toLp 2 (V x))+
      (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (derivativeMatrix V x)ᵀ) (WithLp.toLp 2 (U x))-
      WithLp.toLp 2 (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) := by
  ext k
  change halfDiff k (vectorPair U V) x =
    (∑i,halfDiff k (fun y=>U y i) x*V x i)+
    (∑i,halfDiff k (fun y=>V y i) x*U x i)-
    2*spin x k*∑i,halfDiff k (fun y=>U y i) x*halfDiff k (fun y=>V y i) x
  have hh : halfDiff k (vectorPair U V) x=∑i,halfDiff k (fun y=>U y i*V y i) x := by
    simp only [halfDiff,vectorPair]
    rw [← Finset.sum_sub_distrib,Finset.sum_div]
  rw [hh,← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [halfDiff_mul]
  ring

lemma vectorPair_abs (U V : VectorFields n) (x : Spin n) :
    |vectorPair U V x| ≤ vectorNorm (U x)*vectorNorm (V x) := by
  simpa [vectorPair,vectorNorm,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 (U x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (V x))

lemma vectorPair_cross_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    vectorNorm (fun k=>2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k) ≤
      2*A*B*Real.sqrt (n:ℝ) := by
  have hcol (M : Interaction n) {C : ℝ} (hC : 0≤C) (hM : SKGap.opNorm M≤C) (k : Fin n) :
      vectorNorm (fun i=>M i k)≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [← sq,vectorNorm_sq]
    exact (RandomMatrix.matrix_column_sq_le M k).trans (pow_le_pow_left₀ (norm_nonneg _) hM 2)
  have hdot (k : Fin n) : |∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤A*B := by
    exact (vectorPair_abs (fun _ i=>derivativeMatrix U x i k)
      (fun _ i=>derivativeMatrix V x i k) x).trans
      (mul_le_mul (hcol _ hA hu k) (hcol _ hB hv k) (vectorNorm_nonneg _) hA)
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [← sq,vectorNorm_sq]
  calc
    _ ≤ ∑ _k : Fin n,(2*A*B)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hb : |2*spin x k*∑i,derivativeMatrix U x i k*derivativeMatrix V x i k|≤2*A*B := by
        simpa only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_spin_eq_one,mul_one,one_mul,mul_assoc] using
          mul_le_mul_of_nonneg_left (hdot k) (by norm_num : (0:ℝ)≤2)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by simp [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]; ring

lemma vectorPair_derivative_bound (U V : VectorFields n) (x : Spin n)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B) :
    ‖derivativeVector (vectorPair U V) x‖ ≤
      A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ) := by
  have hop (M : Interaction n) (u : Fin n→ℝ) {C : ℝ} (hM : SKGap.opNorm M≤C) :
      ‖(Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) Mᵀ) (WithLp.toLp 2 u)‖≤C*vectorNorm u := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    change SKGap.opNorm Mᵀ*vectorNorm u≤_
    rw [SKGap.opNorm_transpose]
    exact mul_le_mul_of_nonneg_right hM (vectorNorm_nonneg u)
  rw [vectorPair_derivative]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (hop _ _ hu) (hop _ _ hv)))
    (vectorPair_cross_bound U V x hA hB hu hv))

lemma normalizedPair_derivative (U V : VectorFields n) (x : Spin n) :
    derivativeVector (normalizedPair U V) x =
      (Real.sqrt (n:ℝ))⁻¹ • derivativeVector (vectorPair U V) x := by
  ext k
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,normalizedPair,halfDiff]
  ring

lemma normalizedPair_derivative_bound (hn : 0<n) (U V : VectorFields n) (x : Spin n)
    {A B Cu Cv : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : SKGap.opNorm (derivativeMatrix U x)≤A) (hv : SKGap.opNorm (derivativeMatrix V x)≤B)
    (hU : vectorNorm (U x)≤Cu*Real.sqrt (n:ℝ))
    (hV : vectorNorm (V x)≤Cv*Real.sqrt (n:ℝ)) :
    ‖derivativeVector (normalizedPair U V) x‖≤A*Cv+B*Cu+2*A*B := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [normalizedPair_derivative,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*vectorNorm (V x)+B*vectorNorm (U x)+2*A*B*Real.sqrt (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (vectorPair_derivative_bound U V x hA hB hu hv) (inv_nonneg.mpr hs.le)
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(A*(Cv*Real.sqrt (n:ℝ))+B*(Cu*Real.sqrt (n:ℝ))+2*A*B*Real.sqrt (n:ℝ)) := by
      gcongr
    _ = _ := by field_simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_ResidualPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma mag_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (mag j J h k x)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ)^2 := Finset.sum_le_sum (fun i _=>by
      simpa only [sq_abs,mag] using pow_le_pow_left₀ (abs_nonneg _) (primaryState_mag_bounded j J h k x i) 2)
    _ = _ := by simp

lemma residual_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (residual j J h k x)≤2*Real.sqrt (n:ℝ) := by
  have he : vectorNorm (residual j J h k x)≤vectorNorm (mag j J h k x)+vectorNorm (mag j J h (k+1) x) :=
    norm_sub_le (WithLp.toLp 2 (mag j J h k x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (mag j J h (k+1) x))
  exact he.trans ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualScalarCutoff_bounds (u : ℝ) :
    0 ≤ residualScalarCutoff u ∧ residualScalarCutoff u≤1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (by simp)

lemma residualScalarCutoff_zero {u : ℝ} (hu : 1≤u) : residualScalarCutoff u=0 := by
  simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1-u)*4/3≤0)]

lemma residualScalarCutoff_smooth : ContDiff ℝ ∞ residualScalarCutoff := by
  unfold residualScalarCutoff
  fun_prop

lemma residualScalarCutoff_lipschitz : ∃K,LipschitzWith K residualScalarCutoff := by
  have hc : HasCompactSupport residualScalarCutoff := by
    apply HasCompactSupport.intro' (K:=Set.Icc (-1:ℝ) 1) isCompact_Icc isClosed_Icc
    intro x hx
    simp only [Set.mem_Icc,not_and_or,not_le] at hx
    rcases hx with hx|hx
    · simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1+x)*4/3≤0)]
    · exact residualScalarCutoff_zero hx.le
  exact ContDiff.lipschitzWith_of_hasCompactSupport hc residualScalarCutoff_smooth (by simp)

lemma norm_derivativeVector_sq (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector f x‖^2=∑i,(halfDiff i f x)^2 := by
  exact vectorNorm_sq (fun i=>halfDiff i f x)

lemma derivativeVector_norm_mono (f g : Spin n→ℝ) (x : Spin n) {C : ℝ} (hC : 0≤C)
    (h : ∀i,|halfDiff i f x|≤C*|halfDiff i g x|) :
    ‖derivativeVector f x‖≤C*‖derivativeVector g x‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,norm_derivativeVector_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2

lemma derivativeVector_comp_lipschitz {φ : ℝ→ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector (fun x=>φ (f x)) x‖≤(K:ℝ)*‖derivativeVector f x‖ := by
  apply derivativeVector_norm_mono _ _ _ K.coe_nonneg
  intro i
  have h:=hφ.dist_le_mul (f (replace x i true)) (f (replace x i false))
  simpa only [halfDiff,abs_div,Real.dist_eq,abs_of_pos (by norm_num : (0:ℝ)<2),mul_div_assoc] using
    div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2)

lemma derivativeVector_scale (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*f y) x=c • derivativeVector f x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,halfDiff]
  ring

lemma residualEnergy_as_pair (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    residualEnergy j J h k x =
      (Real.sqrt (n:ℝ))⁻¹*normalizedPair (residual j J h k) (residual j J h k) x := by
  simp only [residualEnergy,vectorNorm_sq,normalizedPair,vectorPair]
  simp only [inv_mul_eq_div,div_div,Real.mul_self_sqrt (Nat.cast_nonneg n),sq]

lemma residualEnergy_gradient (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualEnergy j J h k) x‖≤(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  have he : residualEnergy j J h k=fun y=>(Real.sqrt (n:ℝ))⁻¹*
      normalizedPair (residual j J h k) (residual j J h k) y := funext (residualEnergy_as_pair j J h k)
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hb:=normalizedPair_derivative_bound hn (residual j J h k) (residual j J h k) x hA hA hd hd
    (residual_vectorNorm j J h k x) (residual_vectorNorm j J h k x)
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (by ring)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualStepCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualStepCutoff ρ j J h k x ∧ residualStepCutoff ρ j J h k x≤1 := residualScalarCutoff_bounds _
lemma residualCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualCutoff ρ j J h k x ∧ residualCutoff ρ j J h k x≤1 := by
  have h0:=residualStepCutoff_bounds ρ j J h k x
  have h1:=residualStepCutoff_bounds ρ j J h (k+1) x
  exact ⟨mul_nonneg h0.1 h1.1,(mul_le_mul h0.2 h1.2 h1.1 (by norm_num)).trans_eq (by simp)⟩

lemma derivativeVector_mul_bound (f g : Spin n→ℝ) (x : Spin n)
    (hf : ∀x,|f x|≤1) (hg : ∀x,|g x|≤1) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hdF : ‖derivativeVector f x‖≤A) (hdG : ‖derivativeVector g x‖≤B) :
    ‖derivativeVector (fun y=>f y*g y) x‖≤2*(A+B) := by
  have ht (i : Fin n) : (halfDiff i (fun y=>f y*g y) x)^2≤
      2*(halfDiff i f x)^2+2*(halfDiff i g x)^2 := by
    have hf' : (f (flip x i))^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf (flip x i)) 2
    have hg' : (g x)^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
    rw [halfDiff_mul_flipped]
    nlinarith [mul_le_mul_of_nonneg_right hf' (sq_nonneg (halfDiff i g x)),
      mul_le_mul_of_nonneg_right hg' (sq_nonneg (halfDiff i f x)),
      sq_nonneg (f (flip x i)*halfDiff i g x-g x*halfDiff i f x)]
  have hb : ‖derivativeVector (fun y=>f y*g y) x‖^2≤2*A^2+2*B^2 := by
    calc
      _ ≤ ∑i,(2*(halfDiff i f x)^2+2*(halfDiff i g x)^2) := by
        rw [norm_derivativeVector_sq]; exact Finset.sum_le_sum (fun i _=>ht i)
      _ = 2*‖derivativeVector f x‖^2+2*‖derivativeVector g x‖^2 := by
        simp only [norm_derivativeVector_sq,Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdF 2,pow_le_pow_left₀ (norm_nonneg _) hdG 2]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  nlinarith [mul_nonneg hA hB,sq_nonneg A,sq_nonneg B]

lemma residualStepCutoff_gradient (hn : 0<n) {j ρ : ℝ} (_ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualStepCutoff ρ j J h k) x‖≤
      (K:ℝ)/ρ^2*(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_comp_lipschitz hK (fun y=>residualEnergy j J h k y/ρ^2) x).trans
  have he : (fun y=>residualEnergy j J h k y/ρ^2)=fun y=>(ρ^2)⁻¹*residualEnergy j J h k y := by
    funext y; ring
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (residualEnergy_gradient hn j J h k x hA hd) (inv_nonneg.mpr (sq_nonneg _))) K.coe_nonneg).trans_eq (by ring)

lemma residualCutoff_gradient (hn : 0<n) {j ρ : ℝ} (hρ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h0 : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A)
    (h1 : SKGap.opNorm (derivativeMatrix (residual j J h (k+1)) x)≤B) :
    ‖derivativeVector (residualCutoff ρ j J h k) x‖≤
      (2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*B+2*B^2)))/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_mul_bound _ _ x
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h k y).1];exact (residualStepCutoff_bounds ρ j J h k y).2)
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h (k+1) y).1];exact (residualStepCutoff_bounds ρ j J h (k+1) y).2)
    (by positivity) (by positivity)
    (residualStepCutoff_gradient hn hρ hK J h k x hA h0)
    (residualStepCutoff_gradient hn hρ hK J h (k+1) x hB h1)).trans_eq
  ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Terminal_FinitePairTail
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
variable {n d : ℕ}

lemma RecipeMatrixEvent.mono {j R A A' B W C : ℝ} {M N N' : ℕ} {J : Interaction n}
    (he : RecipeMatrixEvent j R A B W C M N J) (hA : A'≤A) (hN : N'≤N) :
    RecipeMatrixEvent j R A' B W C M N' J := by
  refine ⟨he.1,he.2.1,?_,?_⟩
  · intro w hl hw; exact he.2.2.1 w (hl.trans (by omega)) (wordBounded_mono hw hA)
  · intro w hl hw; exact he.2.2.2 w (hl.trans (by omega)) (wordBounded_mono hw hA)

lemma residualCoefficientBudget_depth_mono (j : ℝ) {k d : ℕ} (hk : k≤d) :
    residualCoefficientBudget j 2 k 0 ≤ residualCoefficientBudget j 2 d 0 := by
  simp only [residualCoefficientBudget,Nat.sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_right₀ (by linarith [steinCoefficientBudget_nonneg |j|]) hk

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Localization_ConstantRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformWeak.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformWeak P (F t)) :
    UniformWeak P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformWeak.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
lemma UniformSquare.finset_sum {τ : Type*} {P : ∀a,Observables (n a)}
    {F : τ→∀a,Observables (n a)} (s : Finset τ) (h : ∀t∈s,UniformSquare P (F t)) :
    UniformSquare P (fun a x=>∑t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformSquare.zero P
  | @insert t s ht ih=>
    simpa only [Finset.sum_insert ht] using (h t (Finset.mem_insert_self ..)).add
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

lemma constantRecipe_source (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M : ℕ) :
    (constantRecipe j J h e M).source 0=fun _=>e := by
  rw [OrdinaryData.source_eq]
  ext x i
  simp [OrdinaryData.sourceOf,constantRecipe,OrdinaryData.seedCoefficient,OrdinaryData.auxCoefficient,coefficient]

lemma constantRecipe_coefficients (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N : ℕ) (x : Spin n) :
    (constantRecipe j J h e M).CoefficientClass N x 1 := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩
  · intro a ha s; exact (segmentRegular_const _ _ x 1).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [SegmentValue,constantRecipe]
  · intros; norm_num [SegmentValue,constantRecipe]

lemma constantRecipe_admissible (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M N p : ℕ) :
    (constantRecipe j J h e M).Admissible N p := by
  intro a ha q hq
  constructor <;> intro s <;> ext x i <;>
    simp [OrdinaryData.seedPartial,OrdinaryData.auxPartial,localPartial,constantRecipe,partialAt]

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma constantRecipe_family (he : ∀a,vectorNorm (e a)≤1) (M p : ℕ) :
    FamilyRecipe j J h (fun a=>constantRecipe j (J a) (h a) (e a) M) 0 p 2 := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
    ⟨1,zero_le_one,?_⟩,fun a x=>(constantRecipe_coefficients j (J a) (h a) (e a) M 0 x).mono (by norm_num),
    fun a=>constantRecipe_admissible j (J a) (h a) (e a) M 0 p⟩
  intro a; simpa [constantRecipe] using he a

lemma primary_residual_telescope (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (d : ℕ) (x : Spin n) (i : Fin n) :
    (∑k∈Finset.range d,residual j J h k x i)=spin x i-mag j J h d x i := by
  induction d with
  | zero=>simp [mag_zero]
  | succ d ih=>rw [Finset.sum_range_succ,ih];dsimp [Primary.residual];ring

theorem gibbs_constant_residuals (d : ℕ) (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a))
    (he : ∀a,vectorNorm (e a)≤1) (k : ℕ) (hk : k≤d) :
    UniformWeak (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) ∧
    UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑i,(spin x i-mag j (J a) (h a) k x i)*e a i) := by
  have H (l : ℕ) (hl : l<k):=
    gibbs_ordinary_residuals l 0 (by norm_num : (2:ℝ)≤2) (by omega : l<d+1)
      hR hB hW hC hn hJ hdiag
      (fun a=>(hevent a).mono (residualCoefficientBudget_depth_mono j (by omega)) (by omega))
      (fun a=>constantRecipe j (J a) (h a) (e a) (d+1)) (constantRecipe_family he (d+1) l)
  have H' (l : ℕ) (hl : l<k) :
      UniformWeak (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) ∧
      UniformSquare (fun a=>fieldGibbs (J a) (h a)) (fun a x=>∑i,residual j (J a) (h a) l x i*e a i) := by
    simpa only [constantRecipe_source] using H l hl
  have hh (a : Ω) (x : Spin (N a)) :
      (∑l∈Finset.range k,∑i,residual j (J a) (h a) l x i*e a i)=
      ∑i,(spin x i-mag j (J a) (h a) k x i)*e a i := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,primary_residual_telescope]
  exact ⟨((UniformWeak.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).1))).congr hh,
    ((UniformSquare.finset_sum (Finset.range k) (fun l hl=>(H' l (Finset.mem_range.mp hl)).2))).congr hh⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
lemma UniformMultiplier.neg {F : ∀a,Observables (n a)} (hF : UniformMultiplier F) :
    UniformMultiplier (fun a x=>-F a x) := by
  obtain ⟨B,L,hB,hL,hF,hd⟩:=hF
  refine ⟨B,L,hB,hL,fun a x=>by simpa using hF a x,fun a x=>?_⟩
  have he (i : Fin (n a)) : halfDiff i (fun y=>-F a y) x= -halfDiff i (F a) x := by unfold halfDiff;ring
  simpa only [he,neg_sq] using hd a x
lemma UniformMultiplier.mul {F G : ∀a,Observables (n a)} (hF : UniformMultiplier F)
    (hG : UniformMultiplier G) : UniformMultiplier (fun a x=>F a x*G a x) := by
  obtain ⟨B,L,hB,hL,hF,hdF⟩:=hF
  obtain ⟨D,K,hD,hK,hG,hdG⟩:=hG
  exact ⟨B*D,Real.sqrt (2*B^2*K^2+2*D^2*L^2),mul_nonneg hB hD,Real.sqrt_nonneg _,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).1,
    fun a=>(scalar_product_bounds (F a) (G a) hB hL hD hK (hF a) (hdF a) (hG a) (hdG a)).2⟩
lemma UniformMultiplier.finset_prod {τ : Type*} {F : τ→∀a,Observables (n a)} (s : Finset τ)
    (h : ∀t∈s,UniformMultiplier (F t)) : UniformMultiplier (fun a x=>∏t∈s,F t a x) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using UniformMultiplier.const (n:=n) 1
  | @insert t s ht ih=>
    simpa only [Finset.prod_insert ht] using (h t (Finset.mem_insert_self ..)).mul
      (ih (fun r hr=>h r (Finset.mem_insert_of_mem hr)))
end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualDerivativeBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0 ≤ residualDerivativeBudget j R B k :=
  add_nonneg (differentiationBound_nonneg hR hB k) (differentiationBound_nonneg hR hB (k+1))

lemma residual_derivative_bound (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    SKGap.opNorm (derivativeMatrix (residual j J h k) x) ≤ residualDerivativeBudget j R B k := by
  have hm (l : ℕ) (hl : l≤k+1) :
      SKGap.opNorm (derivativeMatrix (mag j J h l) x)≤differentiationBound j R B l :=
    (primary_differentiation J h x hn hR hB hJ l (fun t ht=>hformal x t (ht.trans hl))).2.2.1
  rw [show derivativeMatrix (residual j J h k) x=
    derivativeMatrix (mag j J h k) x-derivativeMatrix (mag j J h (k+1)) x from derivativeMatrix_sub _ _ x]
  simp only [opNorm_eq,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hm _ (by omega)) (hm _ le_rfl))

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B ρ : ℝ} {M : ℕ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

lemma residualCutoff_uniform (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B)
    (hn : ∀a,0<N a) (hop : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M→ShapeBound (formalField j (J a) (h a) x l) B)
    (k : ℕ) (hk : k+2<M) :
    UniformMultiplier (fun a=>residualCutoff ρ j (J a) (h a) k) := by
  obtain ⟨K,hK⟩:=residualScalarCutoff_lipschitz
  let A:=residualDerivativeBudget j R B k
  let D:=residualDerivativeBudget j R B (k+1)
  have hA : 0≤A:=residualDerivativeBudget_nonneg hR hB k
  have hD : 0≤D:=residualDerivativeBudget_nonneg hR hB (k+1)
  let L:=2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*D+2*D^2))
  have hL : 0≤L:=by dsimp [L];positivity
  refine ⟨1,L,zero_le_one,hL,fun a x=>?_,fun a x=>?_⟩
  · rw [abs_of_nonneg (residualCutoff_bounds ρ j (J a) (h a) k x).1]
    exact (residualCutoff_bounds ρ j (J a) (h a) k x).2
  · have H:=residualCutoff_gradient (hn a) hρ hK (J a) (h a) k x hA hD
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) k (fun x l hl=>hformal a x l (by omega)) x)
      (residual_derivative_bound (hn a) hR hB (J a) (h a) (hop a) (k+1) (fun x l hl=>hformal a x l (by omega)) x)
    have hone : 1≤Real.sqrt (N a:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn a)
    have hd : ‖derivativeVector (residualCutoff ρ j (J a) (h a) k) x‖≤L :=
      H.trans (div_le_self hL hone)
    simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) hd 2

lemma cutoffWeight_uniform {C : ℕ→∀a,Observables (N a)} (k : ℕ)
    (hC : ∀l≤k,UniformMultiplier (C l)) :
    UniformMultiplier (fun a x=>cutoffWeight (fun l=>C l a x) k) := by
  exact (hC k le_rfl).mul (UniformMultiplier.finset_prod (Finset.range k)
    (fun l hl=>(UniformMultiplier.const 1).add (hC l (Finset.mem_range.mp hl).le).neg))

lemma residualWeight_uniform (hρ : 0<ρ) (hR : 0≤R) (hB : 0≤B)
    (hn : ∀a,0<N a) (hop : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M→ShapeBound (formalField j (J a) (h a) x l) B)
    (k : ℕ) (hk : k+2<M) :
    UniformMultiplier (fun a x=>cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k) := by
  apply cutoffWeight_uniform
  intro l hl
  exact residualCutoff_uniform hρ hR hB hn hop hformal l (by omega)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ074_CM.SKGap_Entropy_WeightedMean
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
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma gibbs_selected_direction_control (d : ℕ) (hρ : 0<ρ)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a))
    (he : ∀a,vectorNorm (e a)≤1) :
    ∃A:ℝ,0≤A ∧ ∀a (f:Observables (N a)),
      |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e a i))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
  have hh : UniformSquare (fun a=>fieldGibbs (J a) (h a))
      (fun a x=>∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e a i)) := by
    apply UniformSquare.finset_sum
    intro k hk
    have hk':k<d-1:=Finset.mem_range.mp hk
    exact (gibbs_constant_residuals d hR hB hW hC hn hJ hdiag hevent he (k+2) (by omega)).2.mul
      (fun a x=>(fieldGibbs_pos _ _ _).le)
      (residualWeight_uniform hρ hR hB hn (fun a=>(hevent a).1)
        (fun a x l hl=>(hevent a).2.1 (h a) x l hl) k (by omega))
  obtain ⟨A,hA,hh⟩:=hh 1 0 zero_le_one le_rfl
  refine ⟨A,hA,fun a f=>?_⟩
  simpa only [mul_one] using hh a f (fun _=>1) (by simp)
    (by intro x;simp [halfDiff])

lemma gibbs_selected_all_directions_s2_oai (d : ℕ) (hρ : 0<ρ)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a)) :
    ∃A:ℝ,0≤A ∧ ∀a (e:Fin (N a)→ℝ),vectorNorm e≤1→∀f:Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e i))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
  let Ω' := (a : Ω) × {e : Fin (N a)→ℝ // vectorNorm e≤1}
  obtain ⟨A,hA,hh⟩:=gibbs_selected_direction_control (Ω:=Ω') (N:=fun a=>N a.1)
    (J:=fun a=>J a.1) (h:=fun a=>h a.1) (e:=fun a=>a.2.val) d hρ hR hB hW hC
    (fun a=>hn a.1) (fun a=>hJ a.1) (fun a=>hdiag a.1) (fun a=>hevent a.1) (fun a=>a.2.property)
  exact ⟨A,hA,fun a e he f=>hh ⟨a,⟨e,he⟩⟩ f⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2_oai.{u} := @OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2_oai.{u}
