-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_finite_labeled_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:59.896741+00:00
-- url     : https://prove2.me/submissions/2d6007c5-817d-438c-91d9-b31603124bbb

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_residual_partition_pos_finite
import Theorems.Thm_OAI_InvariantIsing_cavity_rooted_spectral_linear_moment

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDeficitGap
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a gap in the finite overlap support, the deficit is affine with
slope equal to minus the mass below the gap. Endpoints may be atoms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma deficit_antitone_argument (p : OverlapPath) : Antitone (deficit p) := by
  intro a b hab
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_mono (p.integrable_complement_max b) (p.integrable_complement_max a)
  intro s
  exact sub_le_sub_left (max_le_max_left (p s) hab) 1

lemma deficit_lower_of_ae_le (p : OverlapPath) {M r : ℝ}
    (hM : ∀ᵐ s ∂pathMeasure, p s ≤ M) (hr : r ≤ M) :
    1 - M ≤ deficit p r := by
  rw [deficit_eq_integral]
  calc
    1 - M = ∫ _s : ℝ, (1 - M) ∂pathMeasure := by simp
    _ ≤ ∫ s, 1 - max (p s) r ∂pathMeasure := by
      apply integral_mono_ae (integrable_const _) (p.integrable_complement_max r)
      filter_upwards [hM] with s hs
      exact sub_le_sub_left (max_le hs hr) 1

theorem deficit_affine_on_gap (p : OverlapPath) {a b : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    {r : ℝ} (hr : r ∈ Icc a b) :
    deficit p r = deficit p a - pathMeasure.real {s | p s ≤ a} * (r - a) := by
  let A : Set ℝ := {s | p s ≤ a}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  have he : (fun s => (1 - max (p s) r) - (1 - max (p s) a)) =ᵐ[pathMeasure]
      A.indicator (fun _ => a - r) := by
    filter_upwards [hgap] with s hs
    by_cases hsa : p s ≤ a
    · rw [max_eq_right (hsa.trans hr.1), max_eq_right hsa,
        indicator_of_mem (show s ∈ A from hsa)]
      ring
    · have hbs : b ≤ p s := hs.resolve_left hsa
      rw [max_eq_left (hr.2.trans hbs), max_eq_left (hr.1.trans (hr.2.trans hbs)),
        indicator_of_notMem (show s ∉ A from hsa)]
      ring
  have hi : deficit p r - deficit p a = pathMeasure.real A * (a - r) := by
    rw [deficit_eq_integral, deficit_eq_integral,
      ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max a),
      integral_congr_ae he, integral_indicator_const (a - r) hA]
    rfl
  change deficit p r = deficit p a - pathMeasure.real A * (r - a)
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The noncommuting resolvent identities in the quadratic cavity tilt.
These finite matrix statements include the zero-dimensional convention. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_inverse_pushThrough {d : ℕ} (C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - C * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * C = C * R := by
  calc
    J * C = J * C * ((1 - K * C) * R) := by rw [hR, mul_one]
    _ = (J * (1 - C * K)) * C * R := by noncomm_ring
    _ = C * R := by rw [hJ, one_mul]

lemma cavityResolvent_pushThrough {d : ℕ} (K C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K C = C * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  exact cavity_inverse_pushThrough C K _ _
    (Matrix.nonsing_inv_mul _ hC) (Matrix.mul_nonsing_inv _ hR)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional algebra in `cav:q-factor` and the backward
quadratic recursion.  The factors retain their order: neither the two
covariances nor the quadratic coefficient need commute. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_quadratic_factor {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    1 - (P - C) * cavityBackwardQuadratic K C =
      (1 - P * K) * (1 - C * K)⁻¹ := by
  unfold cavityBackwardQuadratic
  calc
    1 - (P - C) * (K * (1 - C * K)⁻¹) =
        (1 - C * K) * (1 - C * K)⁻¹ -
          (P - C) * (K * (1 - C * K)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hC]
    _ = (1 - P * K) * (1 - C * K)⁻¹ := by noncomm_ring

theorem cavity_quadratic_step_isUnit {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    IsUnit (1 - (P - C) * cavityBackwardQuadratic K C).det := by
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  exact hP.mul (Matrix.isUnit_nonsing_inv_det _ hC)

theorem cavityBackwardQuadratic_transpose {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.transpose = H)
    (hHdet : IsUnit (1 - H * K).det) :
    (cavityBackwardQuadratic K H).transpose = cavityBackwardQuadratic K H := by
  have hKH : IsUnit (1 - K * H).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  unfold cavityBackwardQuadratic
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hH, hK]
  exact cavityResolvent_pushThrough H K hKH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianFactorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite matrix identities connecting standard-Gaussian square
completion with the original, possibly singular, covariance `B Bᵀ`. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_factor_det {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ) :
    (cavityFactorPrecision K B).det = (1 - (B * B.transpose) * K).det := by
  unfold cavityFactorPrecision
  rw [Matrix.det_one_sub_mul_comm (B.transpose * K) B, ← mul_assoc]

/-- The ordered inverse identity required by the square-completion
coefficient. No inverse of the covariance factor is needed. -/
theorem cavity_inverse_factor {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (h : IsUnit (1 - B * A).det) :
    (1 - A * B)⁻¹ = 1 + A * (1 - B * A)⁻¹ * B := by
  apply Matrix.inv_eq_right_inv
  calc
    (1 - A * B) * (1 + A * (1 - B * A)⁻¹ * B) =
        1 + A * ((1 - B * A) * (1 - B * A)⁻¹ - 1) * B := by noncomm_ring
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ h]; simp

theorem cavity_covariance_inverse {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    (1 - (B * B.transpose) * K)⁻¹ =
      1 + B * (cavityFactorPrecision K B)⁻¹ * (B.transpose * K) := by
  have h := cavity_inverse_factor B (B.transpose * K) hQ
  simpa only [cavityFactorPrecision, mul_assoc] using h

theorem cavity_factor_quadratic_coefficient {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    K + K * B * (cavityFactorPrecision K B)⁻¹ * B.transpose * K =
      cavityBackwardQuadratic K (B * B.transpose) := by
  unfold cavityBackwardQuadratic
  rw [cavity_covariance_inverse K B hQ]
  noncomm_ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianIntegral
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar square completion for the quadratic cavity tilt.  The variance
may vanish; only positivity of the resulting precision is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_complete_square (b c d x : ℝ) (hb : b ≠ 0) :
    -b * x ^ 2 + c * x + d =
      -b * (x - c / (2 * b)) ^ 2 + (c ^ 2 / (4 * b) + d) := by
  field_simp [hb]
  ring

lemma cavity_integrable_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + c * x + d)) := by
  have h := ((integrable_exp_neg_mul_sq hb).comp_sub_right (c / (2 * b))).mul_const
    (Real.exp (c ^ 2 / (4 * b) + d))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [← Real.exp_add, cavity_complete_square b c d x hb.ne']

lemma cavity_integral_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2 + c * x + d)) =
      Real.sqrt (Real.pi / b) * Real.exp (c ^ 2 / (4 * b) + d) := by
  simp_rw [cavity_complete_square b c d _ hb.ne', Real.exp_add]
  rw [integral_mul_const, integral_sub_right_eq_self
    (fun x : ℝ => Real.exp (-b * x ^ 2)) (c / (2 * b)), integral_gaussian]

private lemma cavity_gaussian_weighted_integrand (v : ℝ≥0) (a u z : ℝ) :
    gaussianPDFReal 0 v z * Real.exp (a / 2 * (u + z) ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-( (1 - v * a) / (2 * v)) * z ^ 2 +
          (a * u) * z + a * u ^ 2 / 2) := by
  by_cases hv : (v : ℝ) = 0
  · simp [gaussianPDFReal, hv]
  simp only [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp [hv]
  ring

private lemma cavity_gaussian_normalizer (v : ℝ≥0) (a : ℝ)
    (hv : 0 < (v : ℝ)) (hq : 0 < 1 - v * a) :
    (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.sqrt (Real.pi / ((1 - v * a) / (2 * v))) =
      (Real.sqrt (1 - v * a))⁻¹ := by
  calc
    _ = Real.sqrt ((Real.pi / ((1 - v * a) / (2 * v))) /
        (2 * Real.pi * v)) := by
      conv_rhs => rw [Real.sqrt_div' _ (by positivity)]
      ring
    _ = Real.sqrt ((1 - v * a)⁻¹) := by
      congr 1
      field_simp [hv.ne', hq.ne', Real.pi_ne_zero]
    _ = _ := Real.sqrt_inv _

private lemma cavity_gaussian_constant (v a u : ℝ)
    (hq : 1 - v * a ≠ 0) :
    (a * u) ^ 2 / (4 * ((1 - v * a) / (2 * v))) + a * u ^ 2 / 2 =
      a * u ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [hq, hq']
  ring

/-- Exponential integrability includes the degenerate Gaussian. -/
theorem cavity_gaussian_quadratic_integrable (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    Integrable (fun z : ℝ => Real.exp (a / 2 * (u + z) ^ 2)) (gaussianReal 0 v) := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    exact integrable_dirac (by simp)
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (1 - (v : ℝ) * a) / (2 * v) := by positivity
  rw [gaussianReal_of_var_ne_zero 0 hv]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))).2
  simp only [toReal_gaussianPDF, smul_eq_mul]
  simp_rw [cavity_gaussian_weighted_integrand]
  exact (cavity_integrable_exp_quadratic _ _ _ hb).const_mul _

/-- The one-dimensional form of `cav:q-gaussian-integral`, including
singular covariance `v = 0`. -/
theorem cavity_gaussian_quadratic_integral (v : ℝ≥0) (a u : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * (u + z) ^ 2) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ * Real.exp (a * u ^ 2 / (2 * (1 - v * a))) := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
    ring
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (1 - (v : ℝ) * a) / (2 * v) := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [cavity_gaussian_weighted_integrand]
  rw [integral_const_mul, cavity_integral_exp_quadratic _ _ _ hb]
  rw [← mul_assoc, cavity_gaussian_normalizer v a hvpos hq,
    cavity_gaussian_constant v a u hq.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianAffine
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine quadratic Gaussian integrals.  Independent linear terms are
needed after diagonalizing the precision of a noncommuting cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_affine_complete_square (a c d z : ℝ) (ha : a ≠ 0) :
    Real.exp (a / 2 * z ^ 2 + c * z + d) =
      Real.exp (a / 2 * (c / a + z) ^ 2) * Real.exp (d - c ^ 2 / (2 * a)) := by
  rw [← Real.exp_add]
  congr 1
  field_simp [ha]
  ring

private lemma cavity_affine_constant (v a c d : ℝ) (ha : a ≠ 0)
    (hq : 1 - v * a ≠ 0) :
    a * (c / a) ^ 2 / (2 * (1 - v * a)) + (d - c ^ 2 / (2 * a)) =
      d + v * c ^ 2 / (2 * (1 - v * a)) := by
  have hq' : 1 - a * v ≠ 0 := by simpa only [mul_comm] using hq
  field_simp [ha, hq, hq']
  ring

private lemma cavity_gaussian_linear_integral (v : ℝ≥0) (c : ℝ) :
    (∫ z : ℝ, Real.exp (c * z) ∂gaussianReal 0 v) =
      Real.exp (v * c ^ 2 / 2) := by
  simpa only [mgf, zero_mul, zero_add] using
    congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) c

theorem cavity_gaussian_affine_integrable (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    Integrable (fun z : ℝ => Real.exp (a / 2 * z ^ 2 + c * z + d))
      (gaussianReal 0 v) := by
  by_cases ha : a = 0
  · simpa only [ha, zero_div, zero_mul, zero_add, Real.exp_add] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) c).mul_const (Real.exp d)
  simp_rw [cavity_affine_complete_square a c d _ ha]
  exact (cavity_gaussian_quadratic_integrable v a (c / a) hq).mul_const _

theorem cavity_gaussian_affine_integral (v : ℝ≥0) (a c d : ℝ)
    (hq : 0 < 1 - v * a) :
    (∫ z : ℝ, Real.exp (a / 2 * z ^ 2 + c * z + d) ∂gaussianReal 0 v) =
      (Real.sqrt (1 - v * a))⁻¹ *
        Real.exp (d + v * c ^ 2 / (2 * (1 - v * a))) := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, zero_mul, zero_add, mul_zero, sub_zero,
      Real.sqrt_one, inv_one, one_mul, mul_one, Real.exp_add, integral_mul_const]
    rw [cavity_gaussian_linear_integral]
    ring
  simp_rw [cavity_affine_complete_square a c d _ ha]
  rw [integral_mul_const, cavity_gaussian_quadratic_integral v a (c / a) hq,
    mul_assoc, ← Real.exp_add, cavity_affine_constant v a c d ha hq.ne']

theorem cavity_diagonal_gaussian_affine_integrable {d : ℕ}
    (v : Fin d → ℝ≥0) (a c : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    Integrable (fun z : Fin d → ℝ =>
      Real.exp (∑ i, (a i / 2 * z i ^ 2 + c i * z i)))
      (Measure.pi fun i => gaussianReal 0 (v i)) := by
  simp_rw [Real.exp_sum]
  apply Integrable.fintype_prod (f := fun i z => Real.exp (a i / 2 * z ^ 2 + c i * z))
  intro i
  simpa only [add_zero] using cavity_gaussian_affine_integrable (v i) (a i) (c i) 0 (hq i)

theorem cavity_diagonal_gaussian_affine_integral {d : ℕ}
    (v : Fin d → ℝ≥0) (a c : Fin d → ℝ)
    (hq : ∀ i, 0 < 1 - v i * a i) :
    (∫ z : Fin d → ℝ, Real.exp (∑ i, (a i / 2 * z i ^ 2 + c i * z i))
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
      (∏ i, (Real.sqrt (1 - v i * a i))⁻¹) *
        Real.exp (∑ i, v i * c i ^ 2 / (2 * (1 - v i * a i))) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i x => Real.exp (a i / 2 * x ^ 2 + c i * x))]
  have hi i := cavity_gaussian_affine_integral (v i) (a i) (c i) 0 (hq i)
  simp only [add_zero, zero_add] at hi
  simp_rw [hi]
  exact Finset.prod_mul_distrib

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianBasis
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian quadratic integral in arbitrary orthonormal
coordinates.  This is the change-of-basis step for cavity precision. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

private lemma cavity_basis_reconstruct {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (x : Fin d → ℝ) :
    b.repr (∑ i, x i • b i) = WithLp.toLp 2 x := by
  change b.repr (∑ i, (WithLp.toLp 2 x) i • b i) = WithLp.toLp 2 x
  rw [b.sum_repr_symm, b.repr.apply_symm_apply]

private lemma cavity_basis_measurable {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun x : Fin d → ℝ => ∑ i, x i • b i) := by
  fun_prop

theorem cavity_gaussian_basis_integrable {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (a c : Fin d → ℝ) (hq : ∀ i, 0 < 1 - a i) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (∑ i, (a i / 2 * (b.repr x i) ^ 2 + c i * b.repr x i)))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integrable_map_measure (by fun_prop) (cavity_basis_measurable b).aemeasurable]
  simp only [Function.comp_def]
  simp_rw [cavity_basis_reconstruct]
  simpa only [PiLp.toLp_apply, NNReal.coe_one, one_mul] using
    cavity_diagonal_gaussian_affine_integrable (fun _ : Fin d => 1) a c
      (by simpa only [NNReal.coe_one, one_mul] using hq)

theorem cavity_gaussian_basis_integral {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (a c : Fin d → ℝ) (hq : ∀ i, 0 < 1 - a i) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp (∑ i, (a i / 2 * (b.repr x i) ^ 2 + c i * b.repr x i))
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (∏ i, (Real.sqrt (1 - a i))⁻¹) *
        Real.exp (∑ i, c i ^ 2 / (2 * (1 - a i))) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map (cavity_basis_measurable b).aemeasurable (by fun_prop)]
  simp_rw [cavity_basis_reconstruct]
  simpa only [PiLp.toLp_apply, NNReal.coe_one, one_mul] using
    cavity_diagonal_gaussian_affine_integral (fun _ : Fin d => 1) a c
      (by simpa only [NNReal.coe_one, one_mul] using hq)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianSpectral
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square completion for an arbitrary positive definite real precision
matrix, expressed against the standard finite-dimensional Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_eigenbasis_action {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (i : Fin d) :
    Q.toEuclideanLin (hQ.eigenvectorBasis i) =
      hQ.eigenvalues i • hQ.eigenvectorBasis i := by
  ext j
  exact congrFun (hQ.mulVec_eigenvectorBasis i) j

lemma cavity_eigenbasis_coordinate {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.eigenvectorBasis.repr (Q.toEuclideanLin x) i =
      hQ.eigenvalues i * hQ.eigenvectorBasis.repr x i := by
  rw [hQ.eigenvectorBasis.repr_apply_apply, hQ.eigenvectorBasis.repr_apply_apply,
    ← Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ (hQ.eigenvectorBasis i) x,
    cavity_eigenbasis_action Q hQ i, real_inner_smul_left]

lemma cavity_eigenbasis_quadratic {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Q.toEuclideanLin x⟫ =
      ∑ i, hQ.eigenvalues i * (hQ.eigenvectorBasis.repr x i) ^ 2 := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner x (Q.toEuclideanLin x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) x, ← hQ.eigenvectorBasis.repr_apply_apply,
    ← hQ.eigenvectorBasis.repr_apply_apply, cavity_eigenbasis_coordinate]
  ring

lemma cavity_eigenbasis_linear {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (l x : EuclideanSpace ℝ (Fin d)) :
    ⟪l, x⟫ = ∑ i, hQ.eigenvectorBasis.repr l i * hQ.eigenvectorBasis.repr x i := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner l x]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) l, hQ.eigenvectorBasis.repr_apply_apply,
    hQ.eigenvectorBasis.repr_apply_apply]

lemma cavity_eigenbasis_exponent {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (l x : EuclideanSpace ℝ (Fin d)) :
    (‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫ =
      ∑ i, ((1 - hQ.eigenvalues i) / 2 * (hQ.eigenvectorBasis.repr x i) ^ 2 +
        hQ.eigenvectorBasis.repr l i * hQ.eigenvectorBasis.repr x i) := by
  rw [cavity_eigenbasis_quadratic Q hQ, cavity_eigenbasis_linear Q hQ]
  have hn : ‖x‖ ^ 2 = ∑ i, (hQ.eigenvectorBasis.repr x i) ^ 2 := by
    simpa only [hQ.eigenvectorBasis.repr_apply_apply] using
      (hQ.eigenvectorBasis.sum_sq_inner_right x).symm
  rw [hn, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cavity_precision_inverse_cancel {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    Q.toEuclideanLin (Q⁻¹.toEuclideanLin l) = l := by
  ext i
  change (Q *ᵥ (Q⁻¹ *ᵥ fun j => l j)) i = l i
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q
    (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'), Matrix.one_mulVec]

lemma cavity_eigenbasis_inverse_coordinate {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.1.eigenvectorBasis.repr (Q⁻¹.toEuclideanLin l) i =
      hQ.1.eigenvectorBasis.repr l i / hQ.1.eigenvalues i := by
  have hc := cavity_eigenbasis_coordinate Q hQ.1 (Q⁻¹.toEuclideanLin l) i
  rw [cavity_precision_inverse_cancel Q hQ l] at hc
  apply (eq_div_iff (hQ.eigenvalues_pos i).ne').2
  simpa only [mul_comm] using hc.symm

lemma cavity_eigenbasis_inverse_quadratic {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    ⟪l, Q⁻¹.toEuclideanLin l⟫ =
      ∑ i, (hQ.1.eigenvectorBasis.repr l i) ^ 2 / hQ.1.eigenvalues i := by
  rw [cavity_eigenbasis_linear Q hQ.1]
  apply Finset.sum_congr rfl
  intro i _
  rw [cavity_eigenbasis_inverse_coordinate Q hQ l i]
  ring

lemma cavity_precision_normalizer {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) :
    (∏ i, (Real.sqrt (hQ.1.eigenvalues i))⁻¹) = (Real.sqrt Q.det)⁻¹ := by
  rw [Finset.prod_inv_distrib, hQ.1.det_eq_prod_eigenvalues]
  change (∏ i, Real.sqrt (hQ.1.eigenvalues i))⁻¹ =
    (Real.sqrt (∏ i, hQ.1.eigenvalues i))⁻¹
  rw [Real.sqrt_prod _ (fun i _ => (hQ.eigenvalues_pos i).le)]

theorem cavity_gaussian_precision_integrable {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp ((‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  simp_rw [cavity_eigenbasis_exponent Q hQ.1 l]
  exact cavity_gaussian_basis_integrable hQ.1.eigenvectorBasis
    (fun i => 1 - hQ.1.eigenvalues i) (fun i => hQ.1.eigenvectorBasis.repr l i)
    (fun i => by simpa only [sub_sub_cancel] using hQ.eigenvalues_pos i)

/-- Standard-Gaussian square completion with an arbitrary positive definite
precision matrix.  No simultaneous diagonalization with the original
covariance is assumed. -/
theorem cavity_gaussian_precision_integral {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp ((‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt Q.det)⁻¹ * Real.exp (⟪l, Q⁻¹.toEuclideanLin l⟫ / 2) := by
  simp_rw [cavity_eigenbasis_exponent Q hQ.1 l]
  have hp : ∀ i, 0 < 1 - (1 - hQ.1.eigenvalues i) := by
    intro i
    simpa only [sub_sub_cancel] using hQ.eigenvalues_pos i
  rw [cavity_gaussian_basis_integral hQ.1.eigenvectorBasis
    (fun i => 1 - hQ.1.eigenvalues i) (fun i => hQ.1.eigenvectorBasis.repr l i) hp]
  simp only [sub_sub_cancel]
  rw [cavity_precision_normalizer Q hQ, cavity_eigenbasis_inverse_quadratic Q hQ,
    Finset.sum_div]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianFactor
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic Gaussian integration through an arbitrary covariance
factor.  The factor may be singular and need not commute with `K`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_matrix_transpose_inner {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) B.transpose y⟫ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) B x, y⟫ := by
  rw [real_inner_comm y (Matrix.toEuclideanCLM (𝕜 := ℝ) B x),
    Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  exact Matrix.dotProduct_transpose_mulVec B x y

lemma cavity_factor_precision_quadratic {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityFactorPrecision K B) z⟫ =
      ‖z‖ ^ 2 - ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) B z,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ := by
  simp only [cavityFactorPrecision, map_sub, map_one, map_mul,
    sub_apply, one_apply_eq_self,
    mul_apply_eq_comp, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [cavity_matrix_transpose_inner]

lemma cavity_factor_linear_inner {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (u z : EuclideanSpace ℝ (Fin d)) :
    ⟪cavityFactorLinear K B u, z⟫ =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ := by
  unfold cavityFactorLinear
  rw [map_mul, mul_apply_eq_comp]
  calc
    _ = ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) B.transpose (Matrix.toEuclideanCLM (𝕜 := ℝ) K u)⟫ :=
      real_inner_comm _ _
    _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) B z, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ :=
      cavity_matrix_transpose_inner B z _
    _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) K u, Matrix.toEuclideanCLM (𝕜 := ℝ) B z⟫ := real_inner_comm _ _
    _ = _ := Matrix.isSymmetric_toEuclideanLin_iff.mpr hK u _

lemma cavity_factor_exponent {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (u z : EuclideanSpace ℝ (Fin d)) :
    ⟪u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ / 2 =
      (‖z‖ ^ 2 - ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityFactorPrecision K B) z⟫) / 2 +
        ⟪cavityFactorLinear K B u, z⟫ + ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ / 2 := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hK u (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)
  have hc := real_inner_comm (Matrix.toEuclideanCLM (𝕜 := ℝ) K u) (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)
  simp only [map_add, inner_add_left, inner_add_right]
  rw [cavity_factor_precision_quadratic, cavity_factor_linear_inner K B hK]
  change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) K u, Matrix.toEuclideanCLM (𝕜 := ℝ) B z⟫ =
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K (Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ at hs
  linarith

lemma cavity_factor_exponential {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (u z : EuclideanSpace ℝ (Fin d)) :
    Real.exp (⟪u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ / 2) =
      Real.exp ((‖z‖ ^ 2 - ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityFactorPrecision K B) z⟫) / 2 +
        ⟪cavityFactorLinear K B u, z⟫) * Real.exp (⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ / 2) := by
  rw [cavity_factor_exponent K B hK, Real.exp_add]

lemma cavity_factor_completed_quadratic {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (hQ : IsUnit (cavityFactorPrecision K B).det) (u : EuclideanSpace ℝ (Fin d)) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ +
      ⟪cavityFactorLinear K B u,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityFactorPrecision K B)⁻¹ (cavityFactorLinear K B u)⟫ =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (B * B.transpose)) u⟫ := by
  rw [← cavity_factor_quadratic_coefficient K B hQ]
  simp only [map_add, map_mul, add_apply,
    mul_apply_eq_comp, inner_add_right]
  congr 1
  simpa only [cavityFactorLinear, map_mul, mul_apply_eq_comp] using
    cavity_factor_linear_inner K B hK u
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityFactorPrecision K B)⁻¹ (cavityFactorLinear K B u))

theorem cavity_gaussian_factor_integrable {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (hQ : (cavityFactorPrecision K B).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.exp (⟪u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  simp_rw [cavity_factor_exponential K B hK]
  exact (cavity_gaussian_precision_integrable (cavityFactorPrecision K B) hQ
    (cavityFactorLinear K B u)).mul_const _

/-- Square completion with covariance `B Bᵀ`, including singular factors. -/
theorem cavity_gaussian_factor_integral {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (hQ : (cavityFactorPrecision K B).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z)⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt (1 - (B * B.transpose) * K).det)⁻¹ *
        Real.exp (⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityBackwardQuadratic K (B * B.transpose)) u⟫ / 2) := by
  have hdet : IsUnit (cavityFactorPrecision K B).det :=
    isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hgi : (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp ((‖z‖ ^ 2 - ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityFactorPrecision K B) z⟫) / 2 + ⟪cavityFactorLinear K B u, z⟫)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt (cavityFactorPrecision K B).det)⁻¹ *
        Real.exp (⟪cavityFactorLinear K B u, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityFactorPrecision K B)⁻¹ (cavityFactorLinear K B u)⟫ / 2) :=
    cavity_gaussian_precision_integral (cavityFactorPrecision K B) hQ (cavityFactorLinear K B u)
  simp_rw [cavity_factor_exponential K B hK]
  rw [integral_mul_const, hgi, cavity_factor_det, mul_assoc, ← Real.exp_add]
  congr 2
  rw [← cavity_factor_completed_quadratic K B hK hdet u]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultivariateGaussian
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic integral for the actual multivariate Gaussian law.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_covariance_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hs : (CFC.sqrt S).transpose = CFC.sqrt S := by
    have hs' : (CFC.sqrt S).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg S)
    exact Matrix.isHermitian_iff_isSymm.mp hs'.isHermitian
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

theorem cavity_multivariate_gaussian_integrable {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2))
      (multivariateGaussian 0 S) := by
  rw [multivariateGaussian]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, zero_add] using
    cavity_gaussian_factor_integrable K (CFC.sqrt S) hK hQ u

/-- The exact covariance form of `cav:q-factor`, with no inverse of the
covariance and hence no nondegeneracy assumption on it. -/
theorem cavity_multivariate_gaussian_integral {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
      ∂multivariateGaussian 0 S) =
      (Real.sqrt (1 - S * K).det)⁻¹ *
        Real.exp (⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityBackwardQuadratic K S) u⟫ / 2) := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
  simpa only [zero_add, cavity_covariance_sqrt_factor S hS] using
    cavity_gaussian_factor_integral K (CFC.sqrt S) hK hQ u

theorem cavity_multivariate_gaussian_logIntegral {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    Real.log (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
      ∂multivariateGaussian 0 S) =
      -Real.log (1 - S * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K S) u⟫ / 2 := by
  have hd : 0 < (1 - S * K).det := by
    simpa only [cavity_factor_det, cavity_covariance_sqrt_factor S hS] using hQ.det_pos
  rw [cavity_multivariate_gaussian_integral K S hK hS hQ u,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.2 hd).ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt hd.le, Real.log_exp]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine precision homotopy in `cav:q-precision`.  Since the
eigenvectors of its fixed symmetric coefficient do not change, path
nonsingularity rules out eigenvalues at or above one directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_precision_eigenvalues_lt_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) (i : Fin d) :
    hM.eigenvalues i < 1 := by
  by_contra! hEig
  have hEigenPos : 0 < hM.eigenvalues i := lt_of_lt_of_le zero_lt_one hEig
  let t := (hM.eigenvalues i)⁻¹
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(inv_pos.mpr hEigenPos).le, ?_⟩
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hEig
  have hz : (1 - t • M) *ᵥ (fun j => hM.eigenvectorBasis i j) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hM.mulVec_eigenvectorBasis, smul_smul]
    simp [t, inv_mul_cancel₀ hEigenPos.ne']
  have hinj : Function.Injective (1 - t • M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hpath t ht))
  have hvzero : (fun j => hM.eigenvectorBasis i j) = 0 := by
    apply hinj
    simpa only [Matrix.mulVec_zero] using hz
  apply hM.eigenvectorBasis.orthonormal.ne_zero i
  ext j
  exact congrFun hvzero j

lemma cavity_precision_inner_pos {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hEig : ∀ i, hM.eigenvalues i < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) :
    0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ := by
  have he : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ =
      ∑ i, (1 - hM.eigenvalues i) * (hM.eigenvectorBasis.repr x i) ^ 2 := by
    simp only [map_sub, map_one, sub_apply,
      one_apply_eq_self, inner_sub_right, real_inner_self_eq_norm_sq]
    have hq : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) M x⟫ =
        ∑ i, hM.eigenvalues i * (hM.eigenvectorBasis.repr x i) ^ 2 :=
      cavity_eigenbasis_quadratic M hM x
    rw [hq]
    have hn : ‖x‖ ^ 2 = ∑ i, (hM.eigenvectorBasis.repr x i) ^ 2 := by
      simpa only [hM.eigenvectorBasis.repr_apply_apply] using
        (hM.eigenvectorBasis.sum_sq_inner_right x).symm
    rw [hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  obtain ⟨i, hi⟩ : ∃ i, hM.eigenvectorBasis.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply hM.eigenvectorBasis.repr.injective
    ext i
    simpa only [map_zero, PiLp.zero_apply] using h i
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sub_pos.mpr (hEig j)).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (sub_pos.mpr (hEig i)) (sq_pos_of_ne_zero hi)⟩

/-- The source's precision-continuation argument specialized to its actual
affine path. No continuity-of-eigenvalues input is needed. -/
theorem cavity_precision_posDef_of_path {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) :
    (1 - M).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_one.sub hM, ?_⟩
  intro v hv
  have hx : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
    intro h
    apply hv
    ext i
    exact congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  have hp := cavity_precision_inner_pos M hM
    (cavity_precision_eigenvalues_lt_one M hM hpath) (WithLp.toLp 2 v) hx
  simpa only [Matrix.inner_toEuclideanCLM, PiLp.toLp_apply, star_trivial] using hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-gap comparison for the diagonal covariances in the
finite-alphabet cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_inverse_gap {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    (Matrix.diagonal (fun i => (s i)⁻¹) - K).PosDef := by
  have hd : (Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply sub_nonneg.mpr
    simpa only [one_div] using one_div_le_one_div_of_le (hs i) (hsp i)
  have he : Matrix.diagonal (fun i => (s i)⁻¹) - K =
      (Matrix.diagonal (fun i => (p i)⁻¹) - K) +
        Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [he]
  exact hgap.add_posSemidef hd

lemma cavity_diagonal_gap_isUnit {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    IsUnit (1 - Matrix.diagonal s * K).det := by
  have hg := cavity_diagonal_inverse_gap K p s hs hsp hgap
  have he : 1 - Matrix.diagonal s * K =
      Matrix.diagonal s * (Matrix.diagonal (fun i => (s i)⁻¹) - K) := by
    rw [mul_sub, Matrix.diagonal_mul_diagonal]
    have hone : Matrix.diagonal (fun i => s i * (s i)⁻¹) = 1 := by
      simp [funext fun i => mul_inv_cancel₀ (hs i).ne']
    rw [hone]
  rw [he, Matrix.det_mul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (Matrix.PosDef.diagonal hs).det_pos.ne'
  · exact isUnit_iff_ne_zero.mpr hg.det_pos.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStepPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision positivity for a finite-alphabet covariance step.  The
upper covariance is positive diagonal; the lower one is either positive
diagonal or zero, as at the terminal endpoint of the cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_interpolation_isUnit {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (p c : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i) (hcp : ∀ i, c i ≤ p i)
    (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (1 - Matrix.diagonal (fun i => c i + t * (p i - c i)) * K).det := by
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_mul, add_zero]
    rcases hc with hc | hc
    · have hz : c = 0 := funext hc
      simp [hz]
    · exact cavity_diagonal_gap_isUnit K p c hc hcp hgap
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  apply cavity_diagonal_gap_isUnit K p _ _ _ hgap
  · intro i
    have hpi := hp i
    have hci := hc0 i
    nlinarith [mul_pos htpos hpi, mul_nonneg (sub_nonneg.mpr ht.2) hci]
  · intro i
    have hi := hcp i
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hi)]

/-- Positivity of `I-Bᵀ K_i B` from the actual diagonal covariance
ordering and the upper spectral gap.  `B Bᵀ = P-C` may be singular. -/
theorem cavity_step_precision_posDef {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hB : Matrix.diagonal p - Matrix.diagonal c = B * B.transpose) :
    (cavityFactorPrecision (cavityBackwardQuadratic K (Matrix.diagonal c)) B).PosDef := by
  let P := Matrix.diagonal p
  let C := Matrix.diagonal c
  let L := cavityBackwardQuadratic K C
  have hC : IsUnit (1 - C * K).det := by
    simpa only [C, zero_mul, add_zero] using
      cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap 0 (by constructor <;> norm_num)
  have hL : L.transpose = L := by
    exact cavityBackwardQuadratic_transpose K C hK (by simp [C]) hC
  have hM : (B.transpose * L * B).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change (B.transpose * L * B).transpose = B.transpose * L * B
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hL, mul_assoc]
  apply cavity_precision_posDef_of_path (B.transpose * L * B) hM
  intro t ht
  let S := C + t • (P - C)
  have hS : IsUnit (1 - S * K).det := by
    have he : S = Matrix.diagonal (fun i => c i + t * (p i - c i)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [S, C, P]
      · simp [S, C, P, Matrix.diagonal_apply_ne _ hij]
    rw [he]
    exact cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap t ht
  have hstep := cavity_quadratic_step_isUnit K S C hS hC
  have hSC : S - C = t • (P - C) := by dsimp only [S]; abel
  rw [hSC] at hstep
  have hdet : (1 - t • (B.transpose * L * B)).det =
      (1 - (t • (P - C)) * L).det := by
    calc
      _ = (1 - (t • (B.transpose * L)) * B).det := by rw [Matrix.smul_mul]
      _ = (1 - B * (t • (B.transpose * L))).det := Matrix.det_one_sub_mul_comm _ _
      _ = _ := by
        rw [Matrix.mul_smul, ← mul_assoc, ← hB, Matrix.smul_mul]
  rw [hdet]
  exact hstep

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling the covariance step by its positive cascade exponent. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_scaled_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 ≤ ζ) :
    (Real.sqrt ζ • CFC.sqrt S) * (Real.sqrt ζ • CFC.sqrt S).transpose = ζ • S := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hζ, cavity_covariance_sqrt_factor S hS]

lemma cavity_scaled_factor_precision {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    cavityFactorPrecision K (Real.sqrt ζ • B) = cavityFactorPrecision (ζ • K) B := by
  simp only [cavityFactorPrecision, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hζ]

/-- The exact precision required by the Gaussian law, obtained from the
diagonal covariance ordering, including zero covariance increments. -/
theorem cavity_scaled_step_precision {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hΔ : Matrix.diagonal p - Matrix.diagonal c = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic K (Matrix.diagonal c))
      (CFC.sqrt S)).PosDef := by
  rw [← cavity_scaled_factor_precision _ _ ζ hζ]
  apply cavity_step_precision_posDef K (Real.sqrt ζ • CFC.sqrt S) hK
    p c hp hc0 hcp hc hgap
  rw [cavity_scaled_sqrt_factor S hS ζ hζ]
  exact hΔ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper spectral gap supplies the diagonal inverse-gap hypothesis
used by the quadratic cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_upper_spectral_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (L b : ℝ) (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (hb : L < b) : (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosDef := by
  have hp : ((b - L) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hb)
  have he : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      (b - L) • (1 : Matrix (Fin d) (Fin d) ℝ) + (L • 1 - A) := by module
  rw [he]
  exact hp.add_posSemidef hA

lemma cavity_resolvent_diagonal_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (eig : Fin d → ℝ) (L b : ℝ)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) (hb : L < b) :
    (Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig)).PosDef := by
  have he : Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig) = b • (1 : Matrix (Fin d) (Fin d) ℝ) - A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [inv_inv, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact cavity_upper_spectral_gap A L b hA hb

/-- The residual endpoint has lower covariance zero. -/
theorem cavity_resolvent_terminal_precision {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (eig : Fin d → ℝ) (L b : ℝ)
    (hK : (A - Matrix.diagonal eig).transpose = A - Matrix.diagonal eig)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (heig : ∀ i, eig i ≤ L) (hb : L < b)
    (hB : Matrix.diagonal (fun i => (b - eig i)⁻¹) = B * B.transpose) :
    (cavityFactorPrecision (A - Matrix.diagonal eig) B).PosDef := by
  have hp : ∀ i, 0 < (b - eig i)⁻¹ := fun i =>
    inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) hb))
  have h := cavity_step_precision_posDef (A - Matrix.diagonal eig) B hK
    (fun i => (b - eig i)⁻¹) (fun _ => 0) hp (by intro i; exact le_rfl)
    (by intro i; exact (hp i).le) (Or.inl (by intro i; rfl))
    (cavity_resolvent_diagonal_gap A eig L b hA hb) (by simpa using hB)
  simpa only [Matrix.diagonal_zero, cavityBackwardQuadratic_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar resolvent bounds, including the extension at zero.
The comparison uses any alphabet point above the compressed eigenvalue. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityScalarResolvent_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    cavityScalarResolvent ρ eig hρ hρsum α x =
      (finiteInverse ρ eig hρ hρsum x - α)⁻¹ := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hden : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
      x * (finiteInverse ρ eig hρ hρsum x - α) := by
    simp only [finiteR, ite_eq_left hx]
    field_simp [hx.ne']
    ring
  rw [cavityScalarResolvent, hden, div_mul_eq_div_div, div_self hx.ne', one_div]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMatrixResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth resolvent path of a compressed finite-alphabet matrix.
Its norm bounds depend on the alphabet mass, not on the number of cascade levels. -/

noncomputable section
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator MatrixOrder

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

theorem cavitySpectralMatrixPath_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      (finiteInverse ρ eig hρ hρsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hρsum x
  have hb : ∀ i, b - hA.eigenvalues i ≠ 0 := fun i =>
    (sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hdiag : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
      simpa [U] using hA.spectral_theorem.symm
    have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have he : cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      U (Matrix.diagonal (fun i => (b - hA.eigenvalues i)⁻¹)) := by
    simp only [cavitySpectralMatrixPath, cavityScalarResolvent_pos_eq ρ eig hρ hρsum a,
      heig, hx, U, b]
  rw [he]
  symm
  apply Matrix.inv_eq_right_inv
  rw [hdiag, ← map_mul, Matrix.diagonal_mul_diagonal]
  simp [hb]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PoissonCloud
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Cloud. -/

noncomputable section



 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

 
namespace IsingPerceptron

lemma poisson_probability_generating (r : ℝ≥0) (q : ℝ) :
    (∫ n : ℕ, q ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (q - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) * q^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ)*q)^n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ)*(q-1)) := by rw [← Real.exp_add]; congr 1; ring

variable {E : Type*} [MeasurableSpace E]

lemma measurable_cloudSum {ψ : E → ℝ} (hψ : Measurable ψ) :
    Measurable (cloudSum ψ) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℕ → E => ∑ i : Fin n, ψ (y i))
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ => hψ.comp (measurable_pi_apply (i : ℕ)))

lemma iid_finite_laplace (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (n : ℕ) :
    (∫ ω : ℕ → E, Real.exp (-(∑ i : Fin n, ψ (ω i)))
      ∂Measure.infinitePi (fun _ : ℕ => μ)) =
    (∫ x, Real.exp (-ψ x) ∂μ)^n := by
  let X : ℕ → (ℕ → E) → ℝ := fun i ω => Real.exp (-ψ (ω i))
  have hind : iIndepFun X (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (fun _ => hψ.neg.exp)
  have hind' : iIndepFun (fun i : Fin n => X i) (Measure.infinitePi (fun _ : ℕ => μ)) :=
    hind.precomp Fin.val_injective
  have hm (i : Fin n) : AEStronglyMeasurable (X i)
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    ((hψ.neg.exp).comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable
  have he i : (∫ ω, X i ω ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫ x, Real.exp (-ψ x) ∂μ := by
    have mp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
    exact mp.hasLaw.integral_comp hψ.neg.exp.aestronglyMeasurable
  have hh := hind'.integral_fun_prod_eq_prod_integral hm
  simpa only [X, ← Real.exp_sum, ← Finset.sum_neg_distrib, he, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hh

 
theorem finitePoissonCloud_laplace (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, Real.exp (-cloudSum ψ p) ∂finitePoissonCloud r μ) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-ψ x) ∂μ) - 1)) := by
  have hi : Integrable (fun p => Real.exp (-cloudSum ψ p)) (finitePoissonCloud r μ) := by
    apply Integrable.of_bound (measurable_cloudSum hψ |>.neg.exp.aestronglyMeasurable) 1
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => hpos _))
  rw [finitePoissonCloud, integral_prod _ hi]
  simp_rw [cloudSum, iid_finite_laplace μ hψ]
  exact poisson_probability_generating r _

lemma negExp_injective : Function.Injective negExp := by
  intro x y h
  apply EReal.coe_ennreal_injective
  apply neg_injective
  apply EReal.exp_strictMono.injective
  exact (ENNReal.toReal_eq_toReal_iff' (enegExp_ne_top x) (enegExp_ne_top y)).mp h
lemma negExp_ofReal {x : ℝ} (hx : 0 ≤ x) :
    negExp (ENNReal.ofReal x) = Real.exp (-x) := by
  simp [negExp, enegExp, EReal.coe_ennreal_ofReal, max_eq_left hx,
    ← EReal.coe_neg, Real.exp_nonneg]
lemma enegExp_add (x y : ℝ≥0∞) : enegExp (x+y) = enegExp x * enegExp y := by
  by_cases hx : x = ∞
  · simp [hx]
  by_cases hy : y = ∞
  · simp [hy]
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  simp only [enegExp, EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity)]
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe,
    EReal.exp_coe, EReal.exp_coe, neg_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
lemma negExp_add (x y : ℝ≥0∞) : negExp (x+y) = negExp x * negExp y := by
  simp only [negExp, enegExp_add, ENNReal.toReal_mul]
lemma negExp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    negExp (∑ i ∈ s, f i) = ∏ i ∈ s, negExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, negExp_add, ih]
lemma negExp_nat_mul (n : ℕ) (x : ℝ≥0∞) : negExp (n*x) = negExp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, negExp_add, ih, pow_succ]


lemma finiteCloudMeasure_lintegral (p : ℕ × (ℕ → E)) {ψ : E → ℝ≥0∞}
    (hψ : Measurable ψ) : (∫⁻ x, ψ x ∂finiteCloudMeasure p) = ∑ i : Fin p.1, ψ (p.2 i) := by
  simp [finiteCloudMeasure, lintegral_finsetSum_measure, lintegral_dirac' _ hψ]

variable [Nonempty E]


lemma finiteMeasure_mass_normalize (μ : FiniteMeasure E) :
    (μ : Measure E) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure E) := by
  ext s hs
  simpa using congrArg (fun m : FiniteMeasure E => (m : Measure E) s)
    μ.self_eq_mass_smul_normalize

lemma finitePoissonLaw_laplace (μ : FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂finitePoissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E)) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) (μ.normalize : Measure E) := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) (μ.normalize : Measure E) :=
    (integrable_const 1).sub hi
  have hmeas : Measurable (fun ν : Measure E => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [finitePoissonLaw, integral_map measurable_finiteCloudMeasure.aemeasurable
    hmeas.aestronglyMeasurable]
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace μ.mass _ hψ hpos]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost)]
  rw [smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul μ.mass.coe_nonneg,
    negExp_ofReal (mul_nonneg μ.mass.coe_nonneg (integral_nonneg hcost))]
  rw [integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring


omit [Nonempty E] in
lemma laplace_partial_tendsto (P : Measure (ℕ → Measure E)) [IsFiniteMeasure P]
    {a : Measure E → ℝ≥0∞} (ha : Measurable a) :
    Tendsto (fun n => ∫ ω, negExp (∑ i : Fin n, a (ω i)) ∂P)
      atTop (𝓝 (∫ ω, negExp (∑' i, a (ω i)) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    have hm : Measurable (fun ω : ℕ → Measure E => ∑ i : Fin n, a (ω i)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => ha.comp (measurable_pi_apply (i : ℕ)))
    exact (continuous_negExp.measurable.comp hm).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
      exact negExp_le_one _
  · exact ae_of_all _ fun ω => by
      simp_rw [Fin.sum_univ_eq_sum_range (fun i => a (ω i))]
      exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)

lemma poissonProductLaw_laplace_partial (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i) ∂poissonProductLaw μ) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂sfiniteSeq μ i) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind : iIndepFun (fun i (ω : ℕ → Measure E) => negExp (a (ω i))) (poissonProductLaw μ) :=
    iIndepFun_infinitePi (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂poissonProductLaw μ) =
        negExp (∫⁻ x, c x ∂sfiniteSeq μ i) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂poissonComponentLaw μ i :=
        (measurePreserving_eval_infinitePi (poissonComponentLaw μ) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace ⟨sfiniteSeq μ i, inferInstance⟩ hψ hpos
  simpa only [negExp_sum, hei] using hh

 

theorem poissonLaw_laplace (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂poissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂μ) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto (poissonProductLaw μ) ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂sfiniteSeq μ i))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂μ))) := by
    have hsum : (∑' i, ∫⁻ x, c x ∂sfiniteSeq μ i) = ∫⁻ x, c x ∂μ := by
      rw [← lintegral_sum_measure, sum_sfiniteSeq]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂sfiniteSeq μ i)]
    rw [← hsum]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw, integral_map measurable_measureSum.aemeasurable
    heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂poissonProductLaw μ) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a, poissonProductLaw_laplace_partial μ hψ hpos] using hlim) hr


lemma laplace_finite_coordinates_unique {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ k : ι → ℕ,
      (∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂P) =
      ∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂Q) : P = Q := by
  classical
  let g : ι → ((ι → ℝ≥0∞) →ᵇ ℝ) := fun i =>
    negExpBCF.compContinuous ⟨fun x => x i, continuous_apply i⟩
  let ev : MvPolynomial ι ℝ →ₐ[ℝ] ((ι → ℝ≥0∞) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((ι → ℝ≥0∞) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : ι) (x : ι → ℝ≥0∞) : g i x = negExp (x i) := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using
        (fun h => hi (negExp_injective h))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k r =>
    have hev (x : ι → ℝ≥0∞) : ev (MvPolynomial.monomial k r) x =
        r * negExp (∑ i, (k i : ℝ≥0∞) * x i) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [negExp_sum]
      simp only [negExp_nat_mul]
      simp [Finsupp.prod_fintype, hap]
    change (∫ x, ev (MvPolynomial.monomial k r) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k r) x ∂Q
    simp only [hev, integral_const_mul]
    exact congrArg (r * ·) (h fun i => k i)

lemma measure_eq_of_map_eq_comap {E F : Type*} [mE : MeasurableSpace E]
    [mF : MeasurableSpace F] {f : E → F}
    (hf : mE = mF.comap f) {P Q : Measure E} (h : P.map f = Q.map f) : P = Q := by
  have hfm : Measurable f := measurable_iff_comap_le.mpr hf.ge
  ext s hs
  rw [hf] at hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  exact (Measure.map_apply hfm ht).symm.trans ((congrArg (fun μ : Measure F => μ t) h).trans
    (Measure.map_apply hfm ht))

omit [Nonempty E] in
lemma measurable_measureCoordinates : Measurable (measureCoordinates (E := E)) :=
  Measurable.of_eval fun coordinate => Measure.measurable_coe coordinate.2

omit [Nonempty E] in
lemma measureSpace_eq_comap_coordinates :
    (inferInstance : MeasurableSpace (Measure E)) =
      MeasurableSpace.comap measureCoordinates (inferInstance : MeasurableSpace
        ({s : Set E // MeasurableSet s} → ℝ≥0∞)) := by
  apply le_antisymm
  · let m := MeasurableSpace.comap (measureCoordinates (E := E)) inferInstance
    have hc : @Measurable (Measure E) _ m _ measureCoordinates :=
      measurable_iff_comap_le.mpr le_rfl
    have hi : @Measurable (Measure E) (Measure E) m Measure.instMeasurableSpace id := by
      apply @Measure.measurable_of_measurable_coe E (Measure E) _ m id
      intro s hs
      change @Measurable (Measure E) ℝ≥0∞ m _
        (fun ν => measureCoordinates ν ⟨s, hs⟩)
      exact (measurable_pi_apply ⟨s, hs⟩).comp hc
    simpa only [MeasurableSpace.comap_id] using hi.comap_le
  · exact measurable_measureCoordinates.comap_le

omit [Nonempty E] in
 
theorem randomMeasure_laplace_unique (P Q : Measure (Measure E))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ ψ : E → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x) →
      (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂P) =
      ∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂Q) : P = Q := by
  classical
  apply measure_eq_of_map_eq_comap measureSpace_eq_comap_coordinates
  apply IsProjectiveLimit.unique (P := fun I =>
    (P.map measureCoordinates).map I.restrict) (fun _ => rfl)
  intro I
  change (Q.map measureCoordinates).map I.restrict = (P.map measureCoordinates).map I.restrict
  rw [Measure.map_map I.measurable_restrict
      measurable_measureCoordinates,
    Measure.map_map I.measurable_restrict
      measurable_measureCoordinates]
  let e : Measure E → (I → ℝ≥0∞) := fun ν i => ν i.1.1
  have he : Measurable e := Measurable.of_eval fun coordinate =>
    Measure.measurable_coe coordinate.1.2
  change Q.map e = P.map e
  apply laplace_finite_coordinates_unique
  intro k
  let ψ : E → ℝ := fun x => ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x
  have hposi (i : I) (x : E) : 0 ≤ i.1.1.indicator (fun _ => (k i : ℝ)) x := by
    apply indicator_nonneg
    intro _ _
    positivity
  have hpos (x : E) : 0 ≤ ψ x := Finset.sum_nonneg (fun i _ => hposi i x)
  have hm : Measurable ψ := Finset.measurable_sum _ (fun i _ =>
    measurable_const.indicator i.1.2)
  have hoint (ν : Measure E) :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) = ∑ i : I, (k i : ℝ≥0∞) * e ν i := by
    have ho (x : E) : ENNReal.ofReal (ψ x) =
        ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ≥0∞)) x := by
      change ENNReal.ofReal (∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x) = _
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hposi i x)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ i.1.1 <;> simp [hx]
    simp_rw [ho]
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator i.1.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator i.1.2, lintegral_const, Measure.restrict_apply_univ]
  have hcm : Measurable (fun x : I → ℝ≥0∞ => negExp (∑ i, (k i : ℝ≥0∞) * x i)) :=
    continuous_negExp.measurable.comp (Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
  rw [integral_map he.aemeasurable hcm.aestronglyMeasurable,
    integral_map he.aemeasurable hcm.aestronglyMeasurable]
  simpa only [hoint] using (h ψ hm hpos).symm

end IsingPerceptron

 
namespace IsingPerceptron

 

theorem poissonLaw_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : Measure E) [SFinite μ] {T : E → F}
    (hT : Measurable T) [SFinite (μ.map T)] :
    (poissonLaw μ).map (fun ν => ν.map T) = poissonLaw (μ.map T) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun ν : Measure F => negExp (∫⁻ y, ENNReal.ofReal (ψ y) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map (Measure.measurable_map T hT).aemeasurable hm.aestronglyMeasurable]
  simp_rw [lintegral_map hψ.ennreal_ofReal hT]
  rw [poissonLaw_laplace μ (ψ := fun x => ψ (T x)) (hψ.comp hT) (fun x => hpos (T x)),
    poissonLaw_laplace (μ.map T) hψ hpos,
    lintegral_map (by fun_prop) hT]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_LabeledSampling
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function

lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  classical
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a,b) = f (a,b) :=
    fun a b => SimpleFunc.iSup_eapprox_apply hf (a,b)
  simp_rw [← h]
  have he (a : A) : (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) =
      ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun g =>
    Measurable (fun a => ∫⁻ b, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    have hi (a : A) : (∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' t) := by
      simp_rw [← indicator_comp_right (Prod.mk a)]
      rw [lintegral_indicator (ht.preimage measurable_prodMk_left)]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ]
    change Measurable (fun a => ∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a)
    simp_rw [hi]
    exact measurable_const.mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ)
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have ha (a : A) : (∫⁻ b, g₁ (a,b) + g₂ (a,b) ∂κ a) =
        (∫⁻ b, g₁ (a,b) ∂κ a) + ∫⁻ b, g₂ (a,b) ∂κ a :=
      lintegral_add_left (g₁.measurable.comp measurable_prodMk_left) _
    simp_rw [ha]
    exact hm₁.add hm₂


lemma finitePartKernel_finite {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    IsFiniteMeasure (finitePartKernel ν) := by
  by_cases h : ν univ < ∞
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_left h]
    exact ⟨h⟩
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_right h]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_finitePart_lintegral {E : Type*} [MeasurableSpace E]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ν : Measure E => ∫⁻ x, F (x,ν) ∂finitePartKernel ν) :=
  measurable_lintegral_pointwiseFinite finitePartKernel finitePartKernel_finite
    (hF.comp measurable_swap)

lemma infinitePi_indep_eval_rest {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    IndepFun (fun ω : ι → E => ω i)
      (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j) (Measure.infinitePi P) := by
  let m : ι → MeasurableSpace (ι → E) := fun j =>
    MeasurableSpace.comap (fun ω => ω j) inferInstance
  have hi : iIndep m (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (m := m) (fun j => (measurable_pi_apply j).comap_le) hi
    (S := {i}) (T := {j | j ≠ i}) (by simp)
  change Indep (MeasurableSpace.comap (fun ω : ι → E => ω i) inferInstance)
    (MeasurableSpace.comap (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j)
      inferInstance) (Measure.infinitePi P)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_ofPred_eq, m] using h

lemma infinitePi_eval_rest_map {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    (Measure.infinitePi P).map (fun ω : ι → E =>
      (ω i, fun j : {j : ι // j ≠ i} => ω j)) =
      (P i).prod (Measure.infinitePi (fun j : {j : ι // j ≠ i} => P j)) := by
  have hmap := IndepFun.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_eval fun j : {j : ι // j ≠ i} =>
      measurable_pi_apply (j : ι)).aemeasurable (infinitePi_indep_eval_rest P i)
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective] at hmap
  exact hmap

lemma measureSum_eq_eval_add_rest {E : Type*} [MeasurableSpace E]
    (ω : ℕ → Measure E) (i : ℕ) :
    Measure.sum ω = ω i + Measure.sum (fun j : {j : ℕ // j ≠ i} => ω j) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite i]
  congr 1
  trans ∑' j : ℕ, {j : ℕ | j ≠ i}.indicator (fun j => ω j s) j
  · apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [h]
  · exact (tsum_subtype {j : ℕ | j ≠ i} (fun j => ω j s)).symm

variable {E : Type*} [MeasurableSpace E]

lemma measurable_atomCloud (n : ℕ) : Measurable (atomCloud (E := E) (n := n)) := by
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

lemma atomCloud_insertNth {n : ℕ} (i : Fin (n+1)) (x : E) (ω : Fin n → E) :
    atomCloud (i.insertNth x ω) = Measure.dirac x + atomCloud ω := by
  classical
  rw [atomCloud, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

lemma atomCloud_lintegral {n : ℕ} (ω : Fin n → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ x, f x ∂atomCloud ω) = ∑ i, f (ω i) := by
  simp [atomCloud, lintegral_finsetSum_measure, lintegral_dirac' _ hf]

lemma iid_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ ω : Fin (n+1) → E, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  have hm : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    |>.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk
      (measurable_atomCloud (n+1))))
  simp only [Function.comp_apply] at h
  have he (p : E × (Fin n → E)) :
      F (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p) i,
        atomCloud ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p)) =
      F (p.1, Measure.dirac p.1 + atomCloud p.2) := by
    change F ((i.insertNth (α := fun _ => E) p.1 p.2) i,
      atomCloud (i.insertNth (α := fun _ => E) p.1 p.2)) = _
    rw [Fin.insertNth_apply_same, atomCloud_insertNth]
  simp_rw [he] at h
  exact h.symm.trans (lintegral_prod _ hm.aemeasurable)

lemma iid_sum_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) :
    (∫⁻ ω : Fin (n+1) → E, ∑ i, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      (n+1 : ℝ≥0∞) * ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum Finset.univ (f := fun i (ω : Fin (n+1) → E) => F (ω i, atomCloud ω)) (fun i _ =>
    (hF.comp ((measurable_pi_apply i).prodMk (measurable_atomCloud (n+1)))))]
  simp only [iid_point_insertion μ hF n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℝ≥0∞) = r * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have he : (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)) * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [poissonWeight, ENNReal.ofReal_mul (by positivity :
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)),
    ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hh

lemma iid_restrict_lintegral (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ)
    {H : (Fin n → E) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω : ℕ → E, H (fun i => ω i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H ω ∂Measure.pi (fun _ => μ) := by
  have hp : MeasurePreserving (fun ω : ℕ → E => fun i : Fin n => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
    refine ⟨Measurable.of_eval fun index => measurable_pi_apply (index : ℕ), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact hp.lintegral_comp hH

lemma lintegral_finitePoissonCloud (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {H : Measure E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H (finiteCloudMeasure p) ∂finitePoissonCloud r μ) =
      ∑' n, poissonWeight r n * ∫⁻ ω : Fin n → E, H (atomCloud ω)
        ∂Measure.pi (fun _ => μ) := by
  rw [finitePoissonCloud, lintegral_prod (fun p => H (finiteCloudMeasure p)) (hH.comp measurable_finiteCloudMeasure).aemeasurable]
  have hi (n : ℕ) :
      (∫⁻ ω : ℕ → E, H (finiteCloudMeasure (n, ω))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H (atomCloud ω) ∂Measure.pi (fun _ => μ) :=
    iid_restrict_lintegral μ n (hH.comp (measurable_atomCloud n))
  simp_rw [hi]
  rw [poissonMeasure, lintegral_sum_measure]
  simp [lintegral_smul_measure, poissonWeight, smul_eq_mul, lintegral_dirac]

 

theorem finitePoissonCloud_insertion (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F)
    :
    (∫⁻ p, ∫⁻ x, F (x, finiteCloudMeasure p) ∂finitePartKernel (finiteCloudMeasure p)
      ∂finitePoissonCloud r μ) =
      r * ∫⁻ x, ∫⁻ p, F (x, Measure.dirac x + finiteCloudMeasure p)
        ∂finitePoissonCloud r μ ∂μ := by
  rw [lintegral_finitePoissonCloud r μ (measurable_finitePart_lintegral hF)]
  have hm (x : E) : Measurable (fun ν : Measure E => F (x, Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [lintegral_finitePoissonCloud r μ (hm _)]
  have hi (n : ℕ) (ω : Fin n → E) : (∫⁻ x, F (x, atomCloud ω) ∂finitePartKernel (atomCloud ω)) =
      ∑ i, F (ω i, atomCloud ω) := by
    have hfin : IsFiniteMeasure (atomCloud ω) := by unfold atomCloud; infer_instance
    have he : finitePartKernel (atomCloud ω) = atomCloud ω :=
      ite_eq_left (measure_lt_top _ _)
    rw [he]
    exact atomCloud_lintegral ω (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hi]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [iid_sum_point_insertion μ hF, ← mul_assoc, poissonWeight_succ]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmj (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have hmi (n : ℕ) : Measurable (fun x => ∫⁻ ω : Fin n → E,
      F (x, Measure.dirac x + atomCloud ω) ∂Measure.pi (fun _ => μ)) :=
    (hmj n).lintegral_prod_right
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_const_mul _ (hmi n)]
  · intro n
    exact (measurable_const.mul (hmi n)).aemeasurable

lemma measurable_measureSum_countable {ι : Type*} [Countable ι] :
    Measurable (Measure.sum : (ι → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

lemma finitePoissonLaw_finite (μ : FiniteMeasure E) :
    ∀ᵐ ν ∂finitePoissonLaw μ, ν univ < ∞ := by
  rw [finitePoissonLaw, ae_map_iff measurable_finiteCloudMeasure.aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)]
  exact ae_of_all _ fun p => by
    have : IsFiniteMeasure (finiteCloudMeasure p) := by
      unfold finiteCloudMeasure
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    exact measure_lt_top _ _

lemma finitePoissonLaw_insertion (μ : FiniteMeasure E)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂finitePartKernel ν ∂finitePoissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂finitePoissonLaw μ ∂(μ : Measure E) := by
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [finitePoissonLaw, lintegral_map (measurable_finitePart_lintegral hF)
    measurable_finiteCloudMeasure]
  simp_rw [lintegral_map (hm _) measurable_finiteCloudMeasure]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure, smul_eq_mul]
  exact finitePoissonCloud_insertion μ.mass _ hF

 
lemma poissonComponent_insertion (μ : Measure E) [SFinite μ] (i : ℕ)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂finitePartKernel (ω i)
      ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂sfiniteSeq μ i := by
  let R := {j : ℕ // j ≠ i}
  let P := poissonComponentLaw μ
  let rest : (R → Measure E) → Measure E := Measure.sum
  have hrest : Measurable rest := measurable_measureSum_countable
  let joint := fun ω : ℕ → Measure E => (ω i, fun j : R => ω j)
  have hjoint : Measurable joint := (measurable_pi_apply i).prodMk
    (Measurable.of_eval fun index : R => measurable_pi_apply (index : ℕ))
  have hjlaw : (poissonProductLaw μ).map joint =
      (P i).prod (Measure.infinitePi (fun j : R => P j)) :=
    infinitePi_eval_rest_map P i
  have hI : Measurable (fun p : Measure E × (R → Measure E) =>
      ∫⁻ x, F (x,p.1 + rest p.2) ∂finitePartKernel p.1) := by
    apply measurable_finitePart_param measurable_fst (F := fun p => F (p.2,p.1.1 + rest p.1.2))
    exact hF.comp (measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).add
        (hrest.comp (measurable_snd.comp measurable_fst))))
  have hR (x : E) : Measurable (fun p : Measure E × (R → Measure E) =>
      F (x,Measure.dirac x + (p.1 + rest p.2))) :=
    hF.comp (measurable_const.prodMk (measurable_const.add
      (measurable_fst.add (hrest.comp measurable_snd))))
  have he (ω : ℕ → Measure E) : Measure.sum ω = (joint ω).1 + rest (joint ω).2 :=
    measureSum_eq_eval_add_rest ω i
  simp_rw [he]
  rw [← lintegral_map hI hjoint, hjlaw,
    lintegral_prod_symm _ hI.aemeasurable]
  simp_rw [← lintegral_map (hR _) hjoint, hjlaw]
  have hFp (ω : R → Measure E) : Measurable (fun p : E × Measure E =>
      F (p.1,p.2 + rest ω)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hins (ω : R → Measure E) :
      (∫⁻ ν, ∫⁻ x, F (x,ν + rest ω) ∂finitePartKernel ν ∂P i) =
        ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν + rest ω) ∂P i ∂sfiniteSeq μ i :=
    finitePoissonLaw_insertion ⟨sfiniteSeq μ i, inferInstance⟩ (hFp ω)
  simp_rw [hins]
  have hJ : Measurable (fun p : (R → Measure E) × E =>
      ∫⁻ ν, F (p.2,Measure.dirac p.2 + ν + rest p.1) ∂P i) := by
    have hm : Measurable (fun p : ((R → Measure E) × E) × Measure E =>
        F (p.1.2,Measure.dirac p.1.2 + p.2 + rest p.1.1)) :=
      hF.comp ((measurable_snd.comp measurable_fst).prodMk
        (((Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)).add
          measurable_snd).add (hrest.comp (measurable_fst.comp measurable_fst))))
    exact hm.lintegral_prod_right
  rw [lintegral_lintegral_swap hJ.aemeasurable]
  congr 1
  funext x
  rw [lintegral_prod_symm _ (hR x).aemeasurable]
  simp only [add_assoc]

lemma poissonProductLaw_finite (μ : Measure E) [SFinite μ] :
    ∀ᵐ ω ∂poissonProductLaw μ, ∀ i, ω i univ < ∞ := by
  rw [ae_all_iff]
  intro i
  have h := finitePoissonLaw_finite (⟨sfiniteSeq μ i, inferInstance⟩ : FiniteMeasure E)
  have he : (poissonProductLaw μ).map (fun ω => ω i) = poissonComponentLaw μ i :=
    Measure.infinitePi_map_eval _ i
  change ∀ᵐ ν ∂poissonComponentLaw μ i, ν univ < ∞ at h
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)).mp h

 
theorem poissonProductLaw_insertion (μ : Measure E) [SFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂Measure.sum ω ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂μ := by
  have ha : (fun ω : ℕ → Measure E => ∫⁻ x, F (x,Measure.sum ω) ∂Measure.sum ω) =ᵐ[
      poissonProductLaw μ] (fun ω => ∑' i, ∫⁻ x, F (x,Measure.sum ω) ∂finitePartKernel (ω i)) := by
    filter_upwards [poissonProductLaw_finite μ] with ω hω
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro i
    rw [show finitePartKernel (ω i) = ω i from ite_eq_left (hω i)]
  rw [lintegral_congr_ae ha, lintegral_tsum]
  · simp_rw [poissonComponent_insertion μ _ hF]
    rw [← lintegral_sum_measure, sum_sfiniteSeq]
  · intro i
    apply Measurable.aemeasurable
    apply measurable_finitePart_param (measurable_pi_apply i)
      (F := fun p => F (p.2,Measure.sum p.1))
    exact hF.comp (measurable_snd.prodMk (measurable_measureSum.comp measurable_fst))

lemma poissonProductLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.sum ω s ∂poissonProductLaw μ) = μ s := by
  have hF : Measurable (fun p : E × Measure E => s.indicator (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator hs).comp measurable_fst
  have h := poissonProductLaw_insertion μ hF
  simpa only [lintegral_indicator_const hs, one_mul, lintegral_const,
    measure_univ, mul_one] using h

lemma poissonLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ν, ν s ∂poissonLaw μ) = μ s := by
  rw [poissonLaw, lintegral_map (Measure.measurable_coe hs) measurable_measureSum]
  exact poissonProductLaw_mean_count μ hs

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MapWithDensityEquiv
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.powerIntensity_nullSingleton _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ x, w x * f (e x) ∂μ := by
      rw [lintegral_map hf e.measurable]
      exact lintegral_withDensity_eq_lintegral_mul μ hw
        (show Measurable (fun x => f (e x)) from hf.comp e.measurable)
    _ = ∫⁻ x, (w (e.symm x) * f x) ∂μ.map e := by
      simpa only [Pi.mul_apply, Function.comp_apply, e.symm_apply_apply] using
        (lintegral_map (μ := μ) ((hw.comp e.symm.measurable).mul hf) e.measurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (hw.comp e.symm.measurable) hf).symm

lemma measurable_powerIntensityDensity (b : ℝ) : Measurable (powerIntensityDensity b) := by
  unfold powerIntensityDensity
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · fun_prop

lemma powerIntensityDensity_scale {b c : ℝ} (hc : 0 < c) (x : ℝ) :
    ENNReal.ofReal c⁻¹ * powerIntensityDensity b (c⁻¹ * x) =
      ENNReal.ofReal (c ^ b) * powerIntensityDensity b x := by
  have hpos : 0 < c⁻¹ * x ↔ 0 < x := mul_pos_iff_of_pos_left (inv_pos.mpr hc)
  unfold powerIntensityDensity
  by_cases hx : 0 < x
  · simp only [ite_eq_left hx, ite_eq_left (hpos.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le b)]
    congr 1
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    have he : c⁻¹ * c ^ (-(-1-b)) = c ^ b := by
      rw [show -(-1-b) = b + 1 by ring, Real.rpow_add hc]
      simp only [Real.rpow_one]
      field_simp
    calc
       c⁻¹ * (b * (c ^ (-(-1-b)) * x ^ (-1-b))) =
           b * (c⁻¹ * c ^ (-(-1-b))) * x ^ (-1-b) := by ring
       _ = c ^ b * (b * x ^ (-1-b)) := by rw [he]; ring
  · simp only [ite_eq_right hx, ite_eq_right (fun h => hx (hpos.mp h)), ENNReal.ofReal_zero,
      mul_zero]

theorem map_powerIntensity_mul {b c : ℝ} (hc : 0 < c) :
    (powerIntensity b).map (fun x => c*x) =
      ENNReal.ofReal (c ^ b) • powerIntensity b := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm := map_withDensity_equiv e volume (measurable_powerIntensityDensity b)
  change (volume.withDensity (powerIntensityDensity b)).map e = _
  rw [hm]
  change (volume.map (fun x => c*x)).withDensity
    (fun x => powerIntensityDensity b (c⁻¹*x)) = _
  unfold powerIntensity
  rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
    withDensity_smul_measure, ← withDensity_smul (ENNReal.ofReal c⁻¹)
      (show Measurable (fun x => powerIntensityDensity b (c⁻¹*x)) from
        (measurable_powerIntensityDensity b).comp (measurable_const_mul c⁻¹)),
    ← withDensity_smul (ENNReal.ofReal (c^b)) (measurable_powerIntensityDensity b)]
  congr 1
  funext x
  exact powerIntensityDensity_scale hc x

lemma poissonLaw_congr {E : Type*} [MeasurableSpace E] [Nonempty E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν] (h : μ = ν) : poissonLaw μ = poissonLaw ν := by
  subst ν
  rfl

open Set

lemma integrable_power_min {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun x : ℝ => min 1 (max x 0)) (powerIntensity b) := by
  rw [powerIntensity, integrable_withDensity_iff (measurable_powerIntensityDensity b)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hj : IntegrableOn (fun x : ℝ => x ^ (-1-b)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have H₁ : Integrable ((Ioc (0:ℝ) 1).indicator (fun x => b * x ^ (-b))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hi.const_mul b)
  have H₂ : Integrable ((Ioi (1:ℝ)).indicator (fun x => b * x ^ (-1-b))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hj.const_mul b)
  have H := H₁.add H₂
  apply H.congr
  apply ae_of_all
  intro x
  symm
  simp only [Pi.add_apply]
  by_cases hx : 0 < x
  · simp only [powerIntensityDensity, ite_eq_left hx,
      ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)), max_eq_left hx.le]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, indicator_of_mem (show x ∈ Ioc (0:ℝ) 1 from ⟨hx,hx1⟩),
        indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx1), add_zero]
      have hp : x * x ^ (-1-b) = x ^ (-b) := by
        calc
          x * x ^ (-1-b) = x ^ (1 + (-1-b)) := by rw [Real.rpow_add hx, Real.rpow_one]
          _ = x ^ (-b) := by congr 1; ring
      nlinarith [hp]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hx1)), one_mul,
        indicator_of_notMem (show x ∉ Ioc (0:ℝ) 1 from fun h => hx1 h.2),
        indicator_of_mem (show x ∈ Ioi (1:ℝ) from lt_of_not_ge hx1), zero_add]
  · simp [powerIntensityDensity, hx, max_eq_right (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ Ioi (1:ℝ) from fun h => hx (lt_trans zero_lt_one h))]

lemma measurable_stableLaplaceCost : Measurable stableLaplaceCost := by
  unfold stableLaplaceCost
  fun_prop

lemma stableLaplaceCost_nonneg (x : ℝ) : 0 ≤ stableLaplaceCost x := by
  unfold stableLaplaceCost
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _)))

lemma stableLaplaceCost_le_min (x : ℝ) : stableLaplaceCost x ≤ min 1 (max x 0) := by
  unfold stableLaplaceCost
  exact le_min (by linarith [Real.exp_pos (-max x 0)])
    (by linarith [Real.add_one_le_exp (-max x 0)])

lemma integrable_stableLaplaceCost {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable stableLaplaceCost (powerIntensity b) := by
  apply (integrable_power_min hb hb1).mono' measurable_stableLaplaceCost.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stableLaplaceCost_nonneg x)]
    exact stableLaplaceCost_le_min x

lemma stableLaplaceConstant_lt_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ stableLaplaceCost_nonneg)).mp
    (integrable_stableLaplaceCost hb hb1).hasFiniteIntegral

lemma stableLaplaceConstant_pos {b : ℝ} (hb : 0 < b) : 0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant powerIntensity
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_powerIntensityDensity b)
    measurable_stableLaplaceCost.ennreal_ofReal]
  apply (lintegral_pos_iff_support ((measurable_powerIntensityDensity b).mul
    measurable_stableLaplaceCost.ennreal_ofReal)).mpr
  have hs : Function.support (powerIntensityDensity b * (fun x => ENNReal.ofReal (stableLaplaceCost x))) =
      Ioi (0:ℝ) := by
    ext x
    by_cases hx : 0 < x
    · have hp : 0 < b * x ^ (-1-b) := mul_pos hb (Real.rpow_pos_of_pos hx _)
      have hc : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
      simp [Function.mem_support, powerIntensityDensity, stableLaplaceCost, hx,
        max_eq_left hx.le, ne_of_gt (ENNReal.ofReal_pos.mpr hp), ne_of_gt (ENNReal.ofReal_pos.mpr hc)]
    · simp [Function.mem_support, powerIntensityDensity, hx]
  rw [hs]
  simp

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_negExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) : Integrable (fun ω => negExp (X ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_negExp.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖negExp (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
    exact negExp_le_one _

lemma measure_zero_of_integral_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : ℕ → Ω → ℝ} (hfi : ∀ n, Integrable (f n) P)
    (hfpos : ∀ n ω, 0 ≤ f n ω) (hb : ∀ n ω, ω ∈ A → 1 ≤ f n ω)
    (ht : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) : P A = 0 := by
  apply (measureReal_eq_zero_iff (μ := P) (s := A)).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto' ht
  intro n
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) (hfi n)
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω, Pi.one_apply] using hb n ω hω
  · simpa only [indicator_of_notMem hω] using hfpos n ω

theorem stable_laplace_finite_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hl : ∀ t : ℝ, 0 < t →
      (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C * t ^ b)) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  have hi (t : ℝ) : Integrable (fun ω => negExp (ENNReal.ofReal t * X ω)) P :=
    integrable_negExp P (measurable_const.mul hX)
  have hfinite : P {ω | X ω = ∞} = 0 := by
    let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton ∞))
      (f := fun n ω => 1 - negExp (ENNReal.ofReal (t n) * X ω))
    · intro n
      exact (integrable_const 1).sub (hi (t n))
    · intro n ω
      exact sub_nonneg.mpr (negExp_le_one _)
    · intro n ω hω
      change X ω = ∞ at hω
      simp [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (htpos n)))]
    · have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun n => (t n)^b) atTop (𝓝 0) := by
        simpa only [Function.comp_def, Real.zero_rpow hb.ne'] using (Real.continuous_rpow_const hb.le).continuousAt.tendsto.comp ht
      have he : Tendsto (fun n => 1 - Real.exp (-C * (t n)^b)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self] using
          (tendsto_const_nhds (x := (1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-C)))
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      rw [integral_sub (integrable_const 1) (hi (t n)), hl _ (htpos n), integral_const]
      simp
  have hpositive : P {ω | X ω = 0} = 0 := by
    let t : ℕ → ℝ := fun n => (n:ℝ)+1
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton 0))
      (f := fun n ω => negExp (ENNReal.ofReal (t n) * X ω))
    · exact fun n => hi (t n)
    · exact fun _ _ => negExp_nonneg _
    · intro n ω hω
      change X ω = 0 at hω
      simp [hω]
    · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hr := (tendsto_rpow_atTop hb).comp ht
      have he := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hC hr))
      simpa only [hl _ (htpos _), Function.comp_def, neg_mul] using he
  have hf : ∀ᵐ ω ∂P, X ω ≠ ∞ := by simpa only [ae_iff, not_not] using hfinite
  have hp : ∀ᵐ ω ∂P, X ω ≠ 0 := by simpa only [ae_iff, not_not] using hpositive
  filter_upwards [hf, hp] with ω hf hp
  exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hf⟩

lemma stableLaplaceCost_scale (t x : ℝ) (ht : 0 ≤ t) :
    stableLaplaceCost (t*x) = 1-Real.exp (-t * max x 0) := by
  have hm : max (t*x) 0 = t * max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ht).symm
  rw [stableLaplaceCost, hm]
  congr 2
  ring

lemma powerIntensity_laplace_scale {b t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-t * max x 0)) ∂powerIntensity b) =
    ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  simp_rw [← stableLaplaceCost_scale t _ ht.le]
  rw [← lintegral_map measurable_stableLaplaceCost.ennreal_ofReal
    (measurable_const_mul t), map_powerIntensity_mul ht, lintegral_smul_measure]
  rfl

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * X ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hω)

lemma measureReal_mul_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f P) (hfpos : 0 ≤ᵐ[P] f) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, ω ∈ A → c ≤ f ω) : P.real A * c ≤ ∫ ω, f ω ∂P := by
  rw [← smul_eq_mul, ← integral_indicator_const c hA]
  apply integral_mono_ae ((integrable_const c).indicator hA) hf
  filter_upwards [hfpos, hc] with ω hp hb
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω] using hb hω
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hp

lemma stable_laplace_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < X ω} ≤ ENNReal.ofReal (C / (1-Real.exp (-1)) * s^(-b)) := by
  have hc : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hi := integrable_exp_neg_mul P hX hpos (inv_nonneg.mpr hs.le)
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX)
    ((integrable_const 1).sub hi) (by
      filter_upwards [hpos] with ω hω
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [inv_nonneg.mpr hs.le])))
    (1-Real.exp (-1)) (by
      filter_upwards [] with ω hω
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have hmul : 1 < s⁻¹ * X ω := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hs]
        simpa using hω
      linarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi, integral_const, hl _ (inv_pos.mpr hs)] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hbnd : P.real {ω | s < X ω} ≤ C / (1-Real.exp (-1)) * s^(-b) := by
    have he := Real.add_one_le_exp (-C * (s⁻¹)^b)
    have hp : (s⁻¹)^b = s^(-b) := by rw [Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    rw [hp] at h he
    apply (le_of_mul_le_mul_right _ hc)
    calc
      _ ≤ 1-Real.exp (-C * s^(-b)) := h
      _ ≤ C * s^(-b) := by linarith
      _ = (C / (1-Real.exp (-1)) * s^(-b)) * (1-Real.exp (-1)) := by field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma stable_laplace_inverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < (X ω)⁻¹} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-C*s^b)) := by
  have hi := integrable_exp_neg_mul P hX (hpos.mono fun _ h => h.le) hs.le
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX.inv) hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (Real.exp (-1)) (by
      filter_upwards [hpos] with ω hp hω
      apply Real.exp_le_exp.mpr
      have hmul : s * X ω < 1 := by
        simpa only [mul_one] using (lt_inv_mul_iff₀' hp).mp (show s < (X ω)⁻¹ * 1 by simpa using hω)
      linarith)
  rw [hl _ hs] at h
  have hbnd : P.real {ω | s < (X ω)⁻¹} ≤ Real.exp 1 * Real.exp (-C*s^b) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (-1))
    calc
      _ ≤ Real.exp (-C*s^b) := h
      _ = (Real.exp 1 * Real.exp (-C*s^b)) * Real.exp (-1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
        simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma integrable_rpow_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K b r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hrb : r < b)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < X ω} ≤ ENNReal.ofReal (K*t^(-b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator (fun u => u^(r-1)) t +
    (Ioi (1:ℝ)).indicator (fun u => K*u^(r-b-1)) t
  have h₁ : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ => K*t^(r-b-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul K
  have hB : Integrable B (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)).restrict
  have hBpos : ∀ t, 0 ≤ B t := by
    intro t
    apply add_nonneg
    · exact (indicator_nonneg (s := Ioc (0:ℝ) 1) (fun u hu => Real.rpow_nonneg hu.1.le (r-1))) t
    · exact (indicator_nonneg (s := Ioi (1:ℝ)) (fun u hu => mul_nonneg hK (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) (r-b-1)))) t
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hBpos)).mp hB.hasFiniteIntegral
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t ≤ 1
  · have hb : B t = t^(r-1) := by
      simp only [B, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht0,ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr ht1), add_zero]
    rw [hb]
    exact mul_le_of_le_one_left' prob_le_one
  · have hb : B t = K*t^(r-b-1) := by
      simp only [B, indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun h => ht1 h.2),
        indicator_of_mem (show t ∈ Ioi (1:ℝ) from lt_of_not_ge ht1), zero_add]
    rw [hb]
    calc
      _ ≤ ENNReal.ofReal (K*t^(-b)) * ENNReal.ofReal (t^(r-1)) :=
        mul_le_mul_of_nonneg_right (htail t ht0) zero_le
      _ = ENNReal.ofReal (K*t^(r-b-1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ht0.le _)),
          mul_assoc, ← Real.rpow_add ht0]
        rw [show -b + (r-1) = r-b-1 by ring]

lemma integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K C b r : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} ≤ ENNReal.ofReal (K*Real.exp (-C*t^b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun t : ℝ => K * (t^(r-1) * Real.exp (-C*t^b))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hb hC).const_mul K
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ K * (t^(r-1) * Real.exp (-C*t^b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
  apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hnonneg).mp hi.hasFiniteIntegral)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ENNReal.ofReal (K*Real.exp (-C*t^b)) * ENNReal.ofReal (t^(r-1)) :=
      mul_le_mul_of_nonneg_right (htail t ht) zero_le
    _ = ENNReal.ofReal (K*(t^(r-1)*Real.exp (-C*t^b))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
      congr 1
      ring

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hrb : r < b)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => X ω ^ r) P := by
  apply integrable_rpow_of_power_tail P hX hpos (K := C/(1-Real.exp (-1)))
    (div_nonneg hC.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) hr hrb
  exact fun _ ht => stable_laplace_upper_tail P hX hpos hl ht

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b r : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => (X ω)⁻¹ ^ r) P := by
  apply integrable_rpow_of_exp_tail P hX.inv (hpos.mono fun _ h => (inv_pos.mpr h).le)
    (Real.exp_nonneg 1) hC hb hr
  exact fun _ ht => stable_laplace_inverse_tail P hX hpos hl ht

lemma negExp_eq_exp_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : negExp x = Real.exp (-x.toReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx, negExp_ofReal ENNReal.toReal_nonneg]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MarkedPartitionNumerator
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma poissonLaw_ae_intensity (μ : Measure E) [SFinite μ] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν, p x := by
  have he : (∫⁻ ν, ν {x | ¬ p x} ∂poissonLaw μ) = 0 := by
    exact (poissonLaw_mean_count μ (show MeasurableSet {x | ¬p x} from hp.compl)).trans (ae_iff.mp h)
  have hz := (lintegral_eq_zero_iff (Measure.measurable_coe hp.compl)).mp he
  filter_upwards [hz] with ν hν
  exact ae_iff.mpr hν

lemma weightedPoissonTotal_real_eq_ae (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞) {t : ℝ} (ht : 0 ≤ t) :
    (fun ν => ∫⁻ p : ℝ × E, ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal) ∂ν) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal t * weightedPoissonTotal a ν) := by
  have hprod : ∀ᵐ p : ℝ × E ∂(powerIntensity b).prod μ, a p.2 < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt (ha.comp measurable_snd) measurable_const)).mpr
      (ae_of_all _ fun _ => hfin)
  filter_upwards [poissonLaw_ae_intensity ((powerIntensity b).prod μ)
    (measurableSet_lt (ha.comp measurable_snd) measurable_const) hprod] with ν hν
  rw [weightedPoissonTotal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hν] with p hp
  change a p.2 < ∞ at hp
  rw [ENNReal.ofReal_mul (mul_nonneg ht (le_max_right _ _)), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal hp.ne, mul_assoc]

omit [Nonempty E] in
lemma weightedPower_laplace_cost (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (1-Real.exp (-(t * max p.1 0 * (a p.2).toReal)))
      ∂(powerIntensity b).prod μ) =
      ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b := by
  rw [lintegral_prod_symm _ (by fun_prop)]
  have he : (fun y => ∫⁻ x, ENNReal.ofReal
      (1-Real.exp (-(t * max x 0 * (a y).toReal))) ∂powerIntensity b) =ᵐ[μ]
      (fun y => ENNReal.ofReal (t^b) * ENNReal.ofReal ((a y).toReal^b) * stableLaplaceConstant b) := by
    filter_upwards [hpos] with y hy
    have hmul (x : ℝ) : t * max x 0 * (a y).toReal = (t*(a y).toReal)*max x 0 := by ring
    simp_rw [hmul]
    have hs := powerIntensity_laplace_scale (b := b) (mul_pos ht hy)
    simp only [neg_mul] at hs ⊢
    rw [hs, Real.mul_rpow ht.le hy.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_congr_ae he, lintegral_mul_const _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

lemma weightedPoissonTotal_laplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      negExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := poissonLaw_laplace ((powerIntensity b).prod μ)
    (ψ := fun p => t * max p.1 0 * (a p.2).toReal) (by fun_prop)
    (fun p => mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) ENNReal.toReal_nonneg)
  rw [weightedPower_laplace_cost b μ ha hpos ht] at h
  rw [← h]
  apply integral_congr_ae
  exact ((weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp negExp).symm

end IsingPerceptron

namespace IsingPerceptron

end IsingPerceptron

namespace IsingPerceptron

lemma rawCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) :
    (rawCascadeLaw (n+1) b : Measure (RawTree (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod
        (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))) := rfl

lemma HasStableTotal.finite_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  obtain ⟨C, hC, hl⟩ := h
  exact stable_laplace_finite_positive P hX hC hb hl

lemma HasStableTotal.real_laplace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-t * (X ω).toReal) ∂P) = Real.exp (-C*t^b) := by
  have hf := h.finite_positive hX hb
  obtain ⟨C, hC, hl⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [← hl t ht]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]

lemma HasStableTotal.positive_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) : Integrable (fun ω => (X ω).toReal^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  exact stable_positive_moment P hX.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hC hr hrb hl

lemma HasStableTotal.negative_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) : Integrable (fun ω => ((X ω).toReal)⁻¹^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  apply stable_negative_moment P hX.ennreal_toReal _ hC hb hr hl
  filter_upwards [h.finite_positive hX hb] with ω hω
  exact ENNReal.toReal_pos hω.1.ne' hω.2.ne

lemma weightedPoissonTotal_stable {E : Type*} [MeasurableSpace E] [Nonempty E]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) :
    HasStableTotal (poissonLaw ((powerIntensity b).prod μ)) (weightedPoissonTotal a) b := by
  let A := ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ
  have hA : A < ∞ := by
    exact hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
      |>.mp hpay.hasFiniteIntegral
  have hApos : 0 < A := by
    apply (lintegral_pos_iff_support (ha.ennreal_toReal.pow_const b |>.ennreal_ofReal)).mpr
    have he : (Function.support (fun y => ENNReal.ofReal ((a y).toReal^b))) =ᵐ[μ] Set.univ := by
      filter_upwards [hpos] with y hy
      apply propext
      change (ENNReal.ofReal ((a y).toReal^b) ≠ 0) ↔ True
      exact iff_true_intro (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)))
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let C := A * stableLaplaceConstant b
  have hC : C < ∞ := ENNReal.mul_lt_top hA (stableLaplaceConstant_lt_top hb hb1)
  have hCp : 0 < C := ENNReal.mul_pos hApos.ne' (stableLaplaceConstant_pos hb).ne'
  refine ⟨C.toReal, ENNReal.toReal_pos hCp.ne' hC.ne, fun t ht => ?_⟩
  rw [weightedPoissonTotal_laplace b μ ha hfin hpos ht, mul_assoc]
  change negExp (ENNReal.ofReal (t^b) * C) = _
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

theorem rawCascade_total_moments (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    (∀ᵐ T ∂(rawCascadeLaw n b : Measure (RawTree n)),
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) ∧
    (∀ r : ℝ, 0 < r → (∀ i < n, r < b i) →
      Integrable (fun T => (rawTreeTotal n T).toReal^r) (rawCascadeLaw n b : Measure (RawTree n))) ∧
    (∀ r : ℝ, 0 < r → Integrable (fun T => ((rawTreeTotal n T).toReal)⁻¹^r)
      (rawCascadeLaw n b : Measure (RawTree n))) := by
  induction n generalizing b with
  | zero =>
    refine ⟨ae_of_all _ (fun _ => by simp [rawTreeTotal]), ?_, ?_⟩
    · intro r _ _
      simp [rawTreeTotal]
    · intro r _
      simp [rawTreeTotal]
  | succ n ih =>
    have hi := ih (fun i => b (i+1)) hb.tail
    have hb0 := hb.1 0 (by omega)
    have hpos : ∀ᵐ T ∂(rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n)),
        0 < (rawTreeTotal n T).toReal := by
      filter_upwards [hi.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    have hm := hi.2.1 (b 0) hb0.1 (fun i hi => hb.2 0 (i+1) (by omega) (by omega))
    have hs : HasStableTotal (rawCascadeLaw (n+1) b : Measure (RawTree (n+1)))
        (rawTreeTotal (n+1)) (b 0) :=
      weightedPoissonTotal_stable hb0.1 hb0.2 _ (measurable_rawTreeTotal n)
        (hi.1.mono fun _ h => h.2) hpos hm
    exact ⟨hs.finite_positive (measurable_rawTreeTotal _) hb0.1,
      fun r hr hrb => hs.positive_moment (measurable_rawTreeTotal _) hb0.1 hr (hrb 0 (by omega)),
      fun r hr => hs.negative_moment (measurable_rawTreeTotal _) hb0.1 hr⟩

open scoped ProbabilityTheory

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

variable [Nonempty A]

lemma noiseCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) := rfl

lemma noiseCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeForget A n) = rawCascadeLaw n b := by
  induction n generalizing b μ with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw _).map (fun ν => ν.map (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))) = _
    rw [poissonLaw_map _ (T := fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))
      (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd)))]
    apply poissonLaw_congr
    have he : (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2)) =
        Prod.map id (fun q : A × NoiseTree A n => noiseTreeForget A n q.2) := rfl
    rw [he, ← Measure.map_prod_map _ _ (f := id)
      (g := fun q : A × NoiseTree A n => noiseTreeForget A n q.2) measurable_id
      ((measurable_noiseTreeForget A n).comp measurable_snd), Measure.map_id]
    congr 1
    change (((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))).map
        (noiseTreeForget A n ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_noiseTreeForget A n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]

omit [Nonempty A] in
lemma noiseTreeTotal_succ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseTreeTotal A (n+1) ν = ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 ∂ν := by
  change (∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
    ∂ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))) = _
  rw [lintegral_map]
  · rfl
  · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd)
  · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseTreeKeep
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_measure_ae {E : Type*} [MeasurableSpace E] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) : MeasurableSet {ν : Measure E | ∀ᵐ x ∂ν, p x} := by
  simp only [ae_iff]
  exact measurableSet_eq_fun (Measure.measurable_coe hp.compl) measurable_const

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul]

variable (A : Type) [MeasurableSpace A] [Nonempty A]

omit [Nonempty A] in
lemma measurableSet_GoodNoiseTree (n : ℕ) : MeasurableSet {ν | GoodNoiseTree A n ν} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    exact ((measurableSet_lt measurable_const (measurable_noiseTreeTotal A (n+1))).inter
      (measurableSet_lt (measurable_noiseTreeTotal A (n+1)) measurable_const)).inter
        (measurable_measure_ae (ih.preimage (measurable_snd.comp measurable_snd)))

lemma noiseCascade_good (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), GoodNoiseTree A n ν := by
  induction n generalizing b μ with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    have htot : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞ := by
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        (measurable_noiseTreeForget A (n+1)).aemeasurable
      rw [noiseCascadeLaw_forget]
      exact (rawCascade_total_moments (n+1) b hb).1
    have hm : MeasurableSet {p : ℝ × (A × NoiseTree A n) | GoodNoiseTree A n p.2.2} :=
      (measurableSet_GoodNoiseTree A n).preimage (by fun_prop)
    have hdesc : ∀ᵐ p ∂(powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)))), GoodNoiseTree A n p.2.2 := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply ae_of_all
      intro _
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_GoodNoiseTree A n).preimage measurable_snd)).mpr
      exact ae_of_all _ (fun _ => ih (fun j => b (j+1)) hb.tail (fun j => μ (j+1)))
    have hc := poissonLaw_ae_intensity _ hm hdesc
    filter_upwards [htot, hc] with ν ht hd
    exact ⟨ht, hd⟩

omit [Nonempty A] in
lemma noiseChildMass_univ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseChildMass A n ν univ = noiseTreeTotal A (n+1) ν := by
  rw [noiseTreeTotal_succ]
  simp [noiseChildMass, withDensity_apply]

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable (A : Type) [MeasurableSpace A] [Nonempty A]

lemma noiseLeafKernel_succ (n : ℕ) : noiseLeafKernel A (n+1) =
    ((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ noiseLeafKernel A n)) ∘ₖ
      noiseChildKernel A n := rfl

lemma noiseLeafKernel_step (n : ℕ) (ν : NoiseTree A (n+1))
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2 ∂noiseChildKernel A n ν := by
  rw [noiseLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  swap
  · exact hF.lintegral_prod_right'
  rw [Kernel.parallelComp_apply, Kernel.id_apply,
    lintegral_prod _ (show AEMeasurable (fun y : A × NoiseLeaf A n => F (p.1,y)) _ from
      (hF.comp measurable_prodMk_left).aemeasurable),
    lintegral_dirac']
  exact (hF.comp measurable_prodMk_left).lintegral_prod_right'

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafTerminal (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafTerminal n X u p.1 p.2) := by
  induction n generalizing X u with
  | zero => exact (hX 0).comp measurable_fst
  | succ n ih =>
    exact (ih (fun i => hX (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))

lemma noiseChildKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : ℝ × (A × NoiseTree A n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂noiseChildKernel A n ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (noiseChildMass A n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, noiseChildMass_univ, noiseChildMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × (A × NoiseTree A n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2) from
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))) hF

lemma noiseLeafKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_step A n ν hF]
  apply noiseChildKernel_lintegral n ν hν
  exact (hF.comp (by fun_prop : Measurable (fun p :
      (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))

lemma measurable_noiseLeafIntegral (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => ∫⁻ v,
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u p.1 v)) ∂noiseLeafKernel A n p.2) :=
  (((measurable_noiseLeafTerminal n hX hu).comp (by fun_prop : Measurable
    (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)))).exp.ennreal_ofReal).lintegral_kernel_prod_right'
      (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma normalizeMass_of_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] : normalizeMass ν = ν := by
  simp [normalizeMass, measure_univ]

lemma normalizeMass_smul {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞)
    (hν : 0 < ν univ ∧ ν univ < ∞) : normalizeMass (c • ν) = normalizeMass ν := by
  have ht : 0 < (c • ν) univ ∧ (c • ν) univ < ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos hc.1.ne' hν.1.ne', ENNReal.mul_lt_top hc.2 hν.2⟩
  rw [normalizeMass, ite_eq_left ht, normalizeMass, ite_eq_left hν,
    Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc.1.ne') (Or.inl hc.2.ne)]
  congr 1
  calc
    c⁻¹ * (ν univ)⁻¹ * c = (c⁻¹*c)*(ν univ)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc.1.ne' hc.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

lemma finitePoissonProduct_laplace_partial {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i)
      ∂Measure.infinitePi (fun i => finitePoissonLaw (μ i))) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ i : Measure E)) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind := iIndepFun_infinitePi (P := fun i => finitePoissonLaw (μ i)) (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂Measure.infinitePi (fun j => finitePoissonLaw (μ j))) =
        negExp (∫⁻ x, c x ∂(μ i : Measure E)) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂finitePoissonLaw (μ i) :=
        (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (μ j)) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace (μ i) hψ hpos
  simpa only [negExp_sum, hei] using hh

theorem finitePoissonProduct_sum_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  let P := Measure.infinitePi (fun n => finitePoissonLaw (μ n))
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto P ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂(μ i : Measure E)))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂Measure.sum (fun n => (μ n : Measure E))))) := by
    rw [lintegral_sum_measure]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂(μ i : Measure E))]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw_laplace _ hψ hpos,
    integral_map measurable_measureSum.aemeasurable heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂P) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a,P,finitePoissonProduct_laplace_partial μ hψ hpos] using hlim) (by simpa only [lintegral_sum_measure] using hr)

lemma finiteCloud_laplace {E : Type*} [MeasurableSpace E] (r : ℝ≥0)
    (ρ : Measure E) [IsProbabilityMeasure ρ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) ∂finitePoissonCloud r ρ) =
      negExp ((r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂ρ) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) ρ := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) ρ := (integrable_const 1).sub hi
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace r ρ hψ hpos,
    ← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg,
    negExp_ofReal (mul_nonneg r.coe_nonneg (integral_nonneg hcost)),
    integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring

lemma finiteCloud_mark_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (r : ℝ≥0) (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((finitePoissonCloud r μ).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) = finitePoissonCloud r (μ.prod ν) := by
  have hj : MeasurePreserving (fun p : (ℕ → E) × (ℕ → F) => fun i => (p.1 i,p.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hp := (MeasurePreserving.id (poissonMeasure r)).prod hj
  have ha := measurePreserving_prodAssoc (poissonMeasure r)
    (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => ν))
  exact (hp.comp ha).map_eq

lemma finiteCloud_mark_measure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : FiniteMeasure E) (ν : Measure F) [IsProbabilityMeasure ν] :
    ((finitePoissonCloud μ.mass (μ.normalize : Measure E)).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
      finitePoissonLaw ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ := by
  let ξ : FiniteMeasure (E × F) := ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change _ = finitePoissonLaw ξ
  rw [show (fun p : (ℕ × (ℕ → E)) × (ℕ → F) =>
    finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
    finiteCloudMeasure ∘ (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) from rfl,
    ← Measure.map_map measurable_finiteCloudMeasure (by fun_prop),finiteCloud_mark_law]
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun π : Measure (E × F) => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂π)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map measurable_finiteCloudMeasure.aemeasurable hm.aestronglyMeasurable,
    finiteCloud_laplace _ _ hψ hpos,finitePoissonLaw_laplace ξ hψ hpos]
  change _ = negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E).prod ν)
  rw [finiteMeasure_mass_normalize μ,Measure.prod_smul_left,lintegral_smul_measure]
  rfl

lemma measurable_labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] :
    Measurable (labeledMarkedMeasure (E := E) (F := F)) := by
  apply measurable_measureSum.comp
  apply Measurable.of_eval
  intro n
  apply measurable_finiteCloudMeasure.comp
  fun_prop

theorem labeledMarkedMeasure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : ℕ → FiniteMeasure E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    ((labeledPoissonLaw μ).prod (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => ν)))).map labeledMarkedMeasure =
    poissonLaw ((Measure.sum (fun n => (μ n : Measure E))).prod ν) := by
  let f : (ℕ × (ℕ → E)) × (ℕ → F) → Measure (E × F) :=
    fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))
  have hf : Measurable f := measurable_finiteCloudMeasure.comp (by fun_prop)
  have hjoin : Measurable (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := by
    fun_prop
  have hfpi : Measurable (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) :=
    Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))
  have hcomp : (labeledMarkedMeasure (E := E) (F := F)) =
    Measure.sum ∘ (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) ∘
      (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := rfl
  rw [hcomp,← Function.comp_assoc,← Measure.map_map (measurable_measureSum.comp hfpi) hjoin,
    labeledPoissonLaw,infinitePi_prod_join,
    ← Measure.map_map measurable_measureSum hfpi,Measure.infinitePi_map_pi _ (fun _ => hf)]
  simp only [f,finiteCloud_mark_measure_law]
  let η : ℕ → FiniteMeasure (E × F) := fun i => ⟨(μ i : Measure E).prod ν,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_labeledMarkedMeasure <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change (Measure.infinitePi (fun i => finitePoissonLaw (η i))).map Measure.sum = _
  rw [finitePoissonProduct_sum_law η]
  have hcongr {P Q : Measure (E × F)} [SFinite P] [SFinite Q] (h : P = Q) :
      poissonLaw P = poissonLaw Q := by subst Q; rfl
  apply hcongr
  exact (Measure.prod_sum_left _ _).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma intensityComponents_sum {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    Measure.sum (fun n => (intensityComponents μ n : Measure E)) = μ :=
  sum_sfiniteSeq μ

lemma labeledLeafMass_lintegral (n : ℕ) (ω : LabeledTree n) (F : LabeledLeaf n → ℝ≥0∞) :
    (∫⁻ v, F v ∂labeledLeafMass n ω) = ∑' v, labeledLeafWeight n ω v * F v := by
  rw [labeledLeafMass,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) 
    (measurable_of_countable _),lintegral_count]
  rfl

lemma finiteCloud_tsum_weight (ω : WeightCloud) (F : ChildLabel → ℝ≥0∞) :
    (∑' a, childLabelWeight ω a * F a) =
      ∑' m, ∑ i : Fin (ω m).1, ENNReal.ofReal (max ((ω m).2 i) 0) * F (m,i) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro m
  simp only [childLabelWeight,ite_mul,zero_mul]
  rw [tsum_eq_sum (s := Finset.range (ω m).1)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt,ite_true, if_true]
  · intro i hi
    exact ite_eq_right (by simpa using hi)

variable (A : Type) [MeasurableSpace A]

@[fun_prop] lemma measurable_labeledNoiseJoin (n : ℕ) : Measurable (labeledNoiseJoin A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => labeledMarkedMeasure (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))
    apply measurable_labeledMarkedMeasure.comp
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (by fun_prop : Measurable (fun p : LabeledTree (n+1) × MarkForest A (n+1) =>
      (p.2 m i).1)).prodMk (ih.comp (by fun_prop))

lemma infinitePi_prod_join2 {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
      (fun p m i => (p.1 m i,p.2 m i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  rw [show (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m i => (p.1 m i,p.2 m i)) =
      (fun q : ℕ → (ℕ → E) × (ℕ → F) => fun m i => ((q m).1 i,(q m).2 i)) ∘
      (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m => (p.1 m,p.2 m)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join,
    Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : (ℕ → E) × (ℕ → F)) => fun i => (q.1 i,q.2 i))
      (fun _ => by fun_prop)]
  simp_rw [infinitePi_prod_join]

lemma measurePreserving_swap_first_two {E F G : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure F) (ξ : Measure G)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun p : E × (F × G) => (p.2.1,(p.1,p.2.2)))
      (μ.prod (ν.prod ξ)) (ν.prod (μ.prod ξ)) := by
  exact (measurePreserving_prodAssoc ν μ ξ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ξ)).comp
      (measurePreserving_prodAssoc μ ν ξ).symm)

theorem labeledNoiseJoin_law [Nonempty A] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw A n μ)).map (labeledNoiseJoin A n) = noiseCascadeLaw A n b μ := by
  induction n generalizing b μ with
  | zero =>
    change ((Measure.dirac (PUnit.unit : PUnit)).prod (Measure.dirac (PUnit.unit : PUnit))).map
      (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let b' := fun j => b (j+1)
    let μ' := fun j => μ (j+1)
    let L : Measure (LabeledTree n) := labeledCascadeLaw n b'
    let M : Measure (MarkForest A n) := markForestLaw A n μ'
    let R : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let W := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))
    have hi : MeasurePreserving (labeledNoiseJoin A n) (L.prod M) R :=
      ⟨measurable_labeledNoiseJoin A n,ih b' μ'⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp
      (measurePreserving_swap_first_two L (μ 0 : Measure A) M)
    have hmap : (L.prod ((μ 0 : Measure A).prod M)).map
        (fun p => (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) = (μ 0 : Measure A).prod R := hp.map_eq
    have hpi : MeasurePreserving
        (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2)))
        ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L))).prod
          (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := by
      refine ⟨Measurable.of_eval (fun m => Measurable.of_eval (fun i =>
        (by fun_prop : Measurable (fun p : (ℕ → ℕ → LabeledTree n) ×
            (ℕ → ℕ → A × MarkForest A n) => (p.2 m i).1)).prodMk
          ((measurable_labeledNoiseJoin A n).comp (by fun_prop)))),?_⟩
      rw [show (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2))) =
          (fun q : ℕ → ℕ → LabeledTree n × (A × MarkForest A n) => fun m i =>
            ((q m i).2.1,labeledNoiseJoin A n ((q m i).1,(q m i).2.2))) ∘
          (fun p => fun m i => (p.1 m i,p.2 m i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join2,
        Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → LabeledTree n × (A × MarkForest A n)) => fun i =>
          ((q i).2.1,labeledNoiseJoin A n ((q i).1,(q i).2.2))) (fun _ => by fun_prop)]
      simp_rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (p : LabeledTree n × (A × MarkForest A n)) =>
        (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) (fun _ => hp.measurable),hmap]
    have hfull := ((MeasurePreserving.id W).prod hpi).comp
      (measurePreserving_prodAssoc W _ _)
    change ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
      (labeledMarkedMeasure ∘ (fun p => (p.1.1,fun m i =>
        ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))) = _
    have hfm : Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) := hfull.measurable
    rw [← Measure.map_map measurable_labeledMarkedMeasure hfm]
    have hfe : ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
        (fun p => (p.1.1,fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) =
        W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := hfull.map_eq
    rw [hfe,labeledMarkedMeasure_law,noiseCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

lemma infinitePi_triple_curry {I J K A : Type*} [MeasurableSpace A]
    (μ : I → J → K → Measure A) [∀ i j k, IsProbabilityMeasure (μ i j k)] :
    (Measure.infinitePi (fun p : I × (J × K) => μ p.1 p.2.1 p.2.2)).map
      (fun g i j k => g (i,j,k)) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun j => Measure.infinitePi (μ i j))) := by
  rw [show (fun g : (I × (J × K)) → A => fun i j k => g (i,j,k)) =
      (fun q : I → (J × K → A) => fun i j k => q i (j,k)) ∘
      (MeasurableEquiv.curry I (J × K) A) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),Measure.infinitePi_map_curry
      (fun (i : I) (p : J × K) => μ i p.1 p.2)]
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : I) (q : J × K → A) => fun j k => q (j,k))
    (fun _ => by fun_prop)]
  simp only [show (fun q : J × K → A => fun j k => q (j,k)) =
    MeasurableEquiv.curry J K A from rfl,Measure.infinitePi_map_curry]

variable (A : Type) [MeasurableSpace A]

theorem markForestOfCoords_law (n : ℕ) (μ : ℕ → ProbabilityMeasure A) :
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))).map
      (markForestOfCoords A n) = markForestLaw A n μ := by
  induction n generalizing μ with
  | zero =>
    change (Measure.infinitePi _).map (fun _ => (PUnit.unit : PUnit)) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let μ' := fun j => μ (j+1)
    let ν : ForestVertex n → Measure A := fun v => μ' (forestVertexDepth n v)
    have (i : Option (ForestVertex n)) : IsProbabilityMeasure (i.elim (μ 0 : Measure A) ν) := by
      cases i <;> dsimp <;> infer_instance
    have hi : MeasurePreserving (markForestOfCoords A n) (Measure.infinitePi ν)
        (markForestLaw A n μ') := ⟨measurable_markForestOfCoords A n,ih μ'⟩
    have hs : MeasurePreserving (fun g : Option (ForestVertex n) → A =>
        (g none,fun v => g (some v)))
        (Measure.infinitePi (fun v => v.elim (μ 0 : Measure A) ν))
        ((μ 0 : Measure A).prod (Measure.infinitePi ν)) :=
      ⟨by fun_prop,infinitePi_option_split (μ 0 : Measure A) ν⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp hs
    have hmap : (Measure.infinitePi (fun v : Option (ForestVertex n) =>
        v.elim (μ 0 : Measure A) ν)).map (fun g =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) =
        (μ 0 : Measure A).prod (markForestLaw A n μ') := hp.map_eq
    have hc : (fun v : ForestVertex (n+1) => (μ (forestVertexDepth (n+1) v) : Measure A)) =
        (fun v : ℕ × (ℕ × Option (ForestVertex n)) => v.2.2.elim (μ 0 : Measure A) ν) := by
      funext v
      rcases v with ⟨m,i,v⟩
      cases v <;> rfl
    rw [hc]
    change (Measure.infinitePi (fun v : ℕ × (ℕ × Option (ForestVertex n)) =>
        v.2.2.elim (μ 0 : Measure A) ν)).map
        ((fun q : ℕ → ℕ → Option (ForestVertex n) → A => fun m i =>
          (q m i none,markForestOfCoords A n (fun v => q m i (some v)))) ∘
          (fun g m i v => g (m,i,v))) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_triple_curry
        (fun (_ _ : ℕ) (v : Option (ForestVertex n)) => v.elim (μ 0 : Measure A) ν),
      Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → Option (ForestVertex n) → A) =>
        fun i => (q i none,markForestOfCoords A n (fun v => q i (some v)))) (fun _ => by fun_prop)]
    simp_rw [Measure.infinitePi_map_pi _
        (f := fun (_ : ℕ) (g : Option (ForestVertex n) → A) =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) (fun _ => hp.measurable),hmap]
    rfl

end IsingPerceptron

namespace IsingPerceptron

theorem labeledNoiseCoordinates_law (A : Type) [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map
      (fun p => labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      noiseCascadeLaw A n b μ := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (markForestOfCoords A n)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
      (markForestLaw A n μ) from ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩)
  change _ = _
  rw [show (fun p : LabeledTree n × (ForestVertex n → A) =>
      labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      (labeledNoiseJoin A n) ∘ Prod.map id (markForestOfCoords A n) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin A n) hp.measurable,hp.map_eq,
    labeledNoiseJoin_law]

lemma labeledMarkedMeasure_lintegral {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F))
    {G : E × F → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G p ∂labeledMarkedMeasure ω) =
      ∑' m, ∑ i : Fin (ω.1 m).1, G ((ω.1 m).2 i,ω.2 m i) := by
  simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hG]

lemma labeledMarkedMeasure_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) {P : E × F → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ p ∂labeledMarkedMeasure ω, P p) :
    ∀ m (i : Fin (ω.1 m).1), P ((ω.1 m).2 i,ω.2 m i) := by
  intro m i
  have hm := (Measure.ae_sum_iff.mp h) m
  rw [finiteCloudMeasure,← Measure.sum_fintype] at hm
  exact (ae_dirac_iff hP).mp ((Measure.ae_sum_iff.mp hm) i)

variable (A : Type) [MeasurableSpace A] [Nonempty A]

theorem labeledLeafMass_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z))) :
    (labeledLeafMass n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) •
        noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  induction n with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral]
    simp [labeledLeafWeight,labeledNoiseLeaf,noiseTreeTotal,
      rawTreeTotal,noiseLeafKernel,noiseLeafKernelData,Kernel.const_apply]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hgood.1 hF]
    have hinner : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    have hg := labeledMarkedMeasure_ae _
      ((measurableSet_GoodNoiseTree A n).preimage (by fun_prop)) hgood.2
    change (∑' v : ChildLabel × LabeledLeaf n,
      (childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2) *
        F ((ω.1 v.1.1).2 v.1.2,((z v.1.1 v.1.2).1,
          labeledNoiseLeaf A n (ω.2 v.1.1 v.1.2,(z v.1.1 v.1.2).2) v.2))) =
      ∫⁻ p : ℝ × (A × NoiseTree A n), ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂
          labeledMarkedMeasure (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2)))
    have hG : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2)) :=
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (measurable_snd.comp measurable_snd))).mul hinner
    rw [labeledMarkedMeasure_lintegral
      (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2))) hG]
    rw [ENNReal.tsum_prod']
    simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]
    apply tsum_congr
    intro m
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := ih (ω.2 m i) (z m i).2 (hg m i)
    have hFi : Measurable (fun v : NoiseLeaf A n => F ((ω.1 m).2 i,((z m i).1,v))) := by fun_prop
    have hh := congrArg (fun ν : Measure (NoiseLeaf A n) => ∫⁻ v, F ((ω.1 m).2 i,((z m i).1,v)) ∂ν) he
    rw [lintegral_map' hFi.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul] at hh
    exact hh

theorem labeledLeafLaw_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞) :
    (labeledLeafLaw n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  have hm := labeledLeafMass_noiseMap A n ω z hgood
  have htot : labeledLeafMass n ω Set.univ = noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) := by
    have he := congrArg (fun ν : Measure (NoiseLeaf A n) => ν Set.univ) hm
    simpa only [Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ,
      Set.preimage_univ,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using he
  rw [labeledLeafLaw,normalizeMass_map _ (measurable_of_countable _) (by simpa only [htot] using ht),
    hm,normalizeMass_smul _ ht (by simp),normalizeMass_of_probability]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {A : Type} [MeasurableSpace A]

lemma noiseLeafMark_labeled (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (v : LabeledLeaf n) (i : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) i = g (edgeAt n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [noiseLeafMark,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_zero]
    · simpa only [noiseLeafMark,Fin.cases_succ,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_succ] using
        ih (ω.2 v.1.1 v.1.2) (fun w => g (v.1.1,v.1.2,some w)) v.2 j

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual quadratic change from the base spectral matrix to the full
spectral matrix, including the derivative which transports the common root. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavity_spectral_shift_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (finiteInverse ρ eig hρ hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hsum x
  have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
    simpa [U] using hA.spectral_theorem.symm
  have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hd : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have hp := Matrix.PosDef.diagonal (fun i =>
    sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a)))
  have hu : IsUnit (Matrix.diagonal (fun i => b - hA.eigenvalues i)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  change IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det
  rw [hd]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hu.map U.toRingHom)

lemma cavity_spectral_tilt_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (1 - cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ x * (A - A₀)).det := by
  let b := finiteInverse ρ eig hρ hsum x
  let D₀ := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have h₀ : IsUnit D₀.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A₀ hA₀ a heig₀ hx
  have h : IsUnit D.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A hA a heig hx
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx]
  change IsUnit (1 - D₀⁻¹ * (A - A₀)).det
  have he : 1 - D₀⁻¹ * (A - A₀) = D₀⁻¹ * D := by
    calc
      _ = D₀⁻¹ * D₀ - D₀⁻¹ * (A - A₀) := by rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by dsimp only [D, D₀]; noncomm_ring
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalSpectralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precision assumptions in the rooted Gaussian calculation follow
from the actual upper spectral gap when the base matrix is diagonal. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma finiteInverse_antitone_pos {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    finiteInverse ρ eig hρ hsum x ≤ finiteInverse ρ eig hρ hsum y := by
  have hx := hy.trans_le hyx
  by_contra! h
  have hh := finiteResolvent_strictAnti (fun a => (hρ a).le) hsum
    (finiteInverse_spec ρ eig hρ hsum hy).1 h
  rw [(finiteInverse_spec ρ eig hρ hsum hx).2,
    (finiteInverse_spec ρ eig hρ hsum hy).2] at hh
  exact (not_lt_of_ge hyx) hh

lemma cavitySpectralMatrixPath_diagonal_pos {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (e : Fin d → ℝ) (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x =
      Matrix.diagonal (fun i => (finiteInverse ρ eig hρ hsum x - e i)⁻¹) := by
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum _ he a heig hx]
  have hshift : finiteInverse ρ eig hρ hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal e = Matrix.diagonal (fun i => finiteInverse ρ eig hρ hsum x - e i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [hshift, Matrix.diagonal_mul_diagonal]
  have hg i : finiteInverse ρ eig hρ hsum x - e i ≠ 0 :=
    (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a))).ne'
  simp [hg]

theorem cavity_diagonal_spectral_step_precision {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a)
    (hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e)
    (hA : (eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x y ζ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hζ : 0 ≤ ζ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hΔ : cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x -
      cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he y = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic (A - Matrix.diagonal e)
      (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he y))
        (CFC.sqrt S)).PosDef := by
  have hx := hy.trans_le hyx
  let b₀ := finiteInverse ρ eig hρ hsum x
  let b₁ := finiteInverse ρ eig hρ hsum y
  have hb₀ : eig a < b₀ := (finiteInverse_spec ρ eig hρ hsum hx).1 a
  have hb₁ : b₀ ≤ b₁ := finiteInverse_antitone_pos ρ eig hρ hsum hy hyx
  rw [cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hy]
  apply cavity_scaled_step_precision (A - Matrix.diagonal e) S hK hS ζ hζ
    (fun i => (b₀ - e i)⁻¹) (fun i => (b₁ - e i)⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt hb₀))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt (hb₀.trans_le hb₁)))).le
  · intro i
    exact inv_anti₀ (sub_pos.mpr ((hemax i).trans_lt hb₀)) (sub_le_sub_right hb₁ (e i))
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt (hb₀.trans_le hb₁)))
  · exact cavity_resolvent_diagonal_gap A e (eig a) b₀ hA hb₀
  · simpa only [cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hx,
      cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hy] using hΔ

theorem cavity_diagonal_spectral_terminal_precision {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a)
    (hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e)
    (hA : (eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (cavityFactorPrecision (A - Matrix.diagonal e)
      (CFC.sqrt (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x))).PosDef := by
  let H := cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x
  have hdiag := cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hx
  have hH : H.PosSemidef := by
    rw [show H = _ from hdiag]
    exact Matrix.PosSemidef.diagonal (fun i => (inv_pos.mpr
      (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a)))).le)
  apply cavity_resolvent_terminal_precision A (CFC.sqrt H) e (eig a)
    (finiteInverse ρ eig hρ hsum x) hK hA hemax ((finiteInverse_spec ρ eig hρ hsum hx).1 a)
  rw [cavity_covariance_sqrt_factor H hH]
  exact hdiag.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltTransport
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized quadratic tilts commute with the Gaussian factor map. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X → Y) (hF : Measurable F)
    (f : Y → ℝ) (hf : Measurable f) :
    (μ.tilted (f ∘ F)).map F = (μ.map F).tilted f := by
  ext s hs
  rw [Measure.map_apply hF hs, tilted_apply_eq_ofReal_integral' _ (hF hs),
    tilted_apply_eq_ofReal_integral' _ hs,
    integral_map hF.aemeasurable hf.exp.aestronglyMeasurable,
    setIntegral_map hs ((hf.exp.div_const _).aestronglyMeasurable) hF.aemeasurable]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite quadratic cascade normalizer from its conditional moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityQuadraticValue {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ) :
    Measurable (cavityQuadraticValue n K H b i) := by
  unfold cavityQuadraticValue
  fun_prop

lemma cavityQuadraticValue_terminal {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticValue n K H b n s =
      ⟪s, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (H n)) s⟫ / 2 := by
  unfold cavityQuadraticValue
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary Gaussian residual is separate from the Poisson levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_residual_integral {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hH : H.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)
        ∂multivariateGaussian 0 H) =
      Real.exp (-Real.log (1 - H * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) u⟫ / 2) := by
  have hi := cavity_multivariate_gaussian_integrable K H hK hQ u
  have hl := cavity_multivariate_gaussian_logIntegral K H hK hH hQ u
  rw [← Real.exp_log (integral_exp_pos hi), hl]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual determinant contribution to the full quadratic normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_noiseLeafTerminal_sum {d : ℕ} (n : ℕ)
    (X : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    noiseLeafTerminal n X (fun _ p => p.1 + p.2) s v = X n (cavityLeafSum n s v) := by
  induction n generalizing X s with
  | zero => rfl
  | succ n ih => exact ih (fun i => X (i + 1)) (s + v.2.1) v.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-integrated partition function in `cav:q-constants`. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_residual_lintegral {d : ℕ}
    (K R : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hR : R.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt R)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ z : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (Real.exp (⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2))
        ∂multivariateGaussian 0 R) =
      ENNReal.ofReal (Real.exp (-Real.log (1 - R * K).det / 2 +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R) u⟫ / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (cavity_multivariate_gaussian_integrable K R hK hQ u)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    cavity_residual_integral K R hK hR hQ u]

lemma cavityResidualPartition_eq_leafIntegral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    cavityResidualPartition n K (H n) s V =
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n
        (fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2)
          (fun _ p => p.1 + p.2) s v))
            ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V := by
  unfold cavityResidualPartition
  apply lintegral_congr
  intro v
  rw [cavity_residual_lintegral K (H n) hK hH hQ,
    cavity_noiseLeafTerminal_sum, cavityQuadraticValue_terminal]
  congr 2
  ring

lemma cavity_noiseTreeTotal_pos_finite {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _),
      0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V ∧
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V < ∞ := by
  apply ae_of_ae_map (μ := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _))
    (p := fun V : RawTree n => 0 < rawTreeTotal n V ∧ rawTreeTotal n V < ∞)
    (measurable_noiseTreeForget (EuclideanSpace ℝ (Fin d)) n).aemeasurable
  rw [noiseCascadeLaw_forget]
  exact (rawCascade_total_moments n b hb).1


lemma measurable_cavityResidualPartition {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.IsHermitian) (hH : (H n).PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityResidualPartition n K (H n) p.1 p.2) := by
  have he : (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityResidualPartition n K (H n) p.1 p.2) = fun p =>
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n
          (fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2)
            (fun _ q => q.1 + q.2) p.1 v))
              ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2 := by
    funext p
    exact cavityResidualPartition_eq_leafIntegral n K H b hK hH hQ p.1 p.2
  rw [he]
  exact measurable_noiseLeafIntegral n
    (fun i => (measurable_cavityQuadraticValue n K H b i).sub_const _)
    (fun _ => measurable_fst.add measurable_snd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOneReplicaPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sampled innovation path has independent Gaussian increments.
This is the marginal needed by the remaining linear-tilt moment bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityLeafSum_eq_mark_sum {d : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n s v = s + ∑ i : Fin n, noiseLeafMark n v i := by
  induction n generalizing s with
  | zero => simp [cavityLeafSum]
  | succ n ih =>
    rw [cavityLeafSum, ih, Fin.sum_univ_succ]
    simp only [noiseLeafMark, Fin.cases_zero, Fin.cases_succ]
    abel

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTilt
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the two successive tilts with the full cavity factor on
the original leaf/residual/spin prior, with the common root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityRootedQuadratic {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) : Measurable (cavityRootedQuadratic n K) :=
  ((measurable_cavityRootedField n).inner
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) K).measurable.comp (measurable_cavityRootedField n))).div_const 2

lemma cavity_residual_quadratic_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    Integrable (fun z => Real.exp (⟪cavityLeafSum n s z.1 + z.2,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s z.1 + z.2)⟫ / 2))
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) := by
  have hm : Measurable (fun z : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => Real.exp (⟪cavityLeafSum n s z.1 + z.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s z.1 + z.2)⟫ / 2)) := by
    exact ((measurable_cavityRootedQuadratic n K).comp
      (measurable_const.prodMk measurable_id)).exp
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  exact hZ

theorem cavity_rooted_quadratic_eq_tilted {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    cavityRootedResidualKernel n K R ω =
      (cavityRootedPriorKernel n R ω).tilted (cavityRootedQuadratic n K) := by
  let μ := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n ω.2).prod
    (multivariateGaussian 0 R)
  let F := fun z : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) => (ω.1, z)
  let Q := cavityRootedQuadratic n K
  have hQ := measurable_cavityRootedQuadratic n K
  have hi := cavity_residual_quadratic_integrable n K R ω.1 ω.2 hZ
  have hg : cavityQuadraticResidualGibbs n K R ω.1 ω.2 = μ.tilted (Q ∘ F) := by
    unfold cavityQuadraticResidualGibbs
    exact normalizeMass_exp μ (Q ∘ F) (hQ.comp (measurable_const.prodMk measurable_id)) hi
  rw [cavityRootedResidualKernel, Kernel.prod_apply, Kernel.deterministic_apply]
  change (Measure.dirac ω.1).prod (cavityQuadraticResidualGibbs n K R ω.1 ω.2) = _
  rw [hg, Measure.dirac_prod]
  have hp : cavityRootedPriorKernel n R ω = μ.map F := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [hp]
  exact cavity_tilt_map μ F (measurable_const.prodMk measurable_id) Q hQ

lemma cavity_tilt_prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) :
    (μ.tilted f).prod ν = (μ.prod ν).tilted (fun z => f z.1) := by
  have he : (∫ z : X × Y, Real.exp (f z.1) ∂μ.prod ν) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := ν) (fun x => Real.exp (f x)))
  rw [Measure.tilted, Measure.tilted,
    prod_withDensity_left (hf.exp.div_const _).ennreal_ofReal,
    he]

lemma cavityQuadratic_eq_inner {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    cavityQuadratic K y = ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2 := by
  have hs : (∑ i, ∑ j, y i * K i j * y j) =
      ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [cavityQuadratic, hs]
  ring

lemma cavity_rooted_exponent_split {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k) :
    cavityRootedQuadratic n K z.1 + cavityLogFactor 0 L C (cavityRootedField n z.1) z.2 =
      cavityLogFactor K L C (cavityRootedField n z.1) z.2 := by
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) (cavityRootedField n z.1) = 0 := by
    simp [cavityQuadratic]
  dsimp only [cavityLogFactor, cavityRootedQuadratic]
  rw [hz, cavityQuadratic_eq_inner K (cavityRootedField n z.1)]
  ring

lemma cavity_rooted_quadratic_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    Integrable (fun z => Real.exp (cavityRootedQuadratic n K z))
      (cavityRootedPriorKernel n R ω) := by
  have hraw := cavity_residual_quadratic_integrable n K R ω.1 ω.2 hZ
  have hp : cavityRootedPriorKernel n R ω =
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n ω.2).prod
        (multivariateGaussian 0 R)).map (fun z => (ω.1, z)) := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [hp]
  exact (integrable_map_measure ((measurable_cavityRootedQuadratic n K).exp.aestronglyMeasurable)
    (measurable_const.prodMk measurable_id).aemeasurable).mpr hraw

theorem cavity_rooted_full_tilt_eq {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞) :
    ((cavityRootedResidualKernel n K R ω).prod π).tilted
        (fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2) =
      ((cavityRootedPriorKernel n R ω).prod π).tilted
        (fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  let μ := cavityRootedPriorKernel n R ω
  let Q := fun z : (EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k =>
    cavityRootedQuadratic n K z.1
  have hi : Integrable (fun z => Real.exp (Q z)) (μ.prod π) := by
    exact (cavity_rooted_quadratic_integrable n K R ω hZ).comp_fst π
  rw [cavity_rooted_quadratic_eq_tilted n K R ω hZ,
    cavity_tilt_prod_left _ π _ (measurable_cavityRootedQuadratic n K), tilted_tilted hi]
  congr 1
  funext z
  change cavityRootedQuadratic n K z.1 +
    cavityLogFactor 0 L C (cavityRootedField n z.1) z.2 = _
  exact cavity_rooted_exponent_split n K L C z

theorem cavity_rooted_full_exp_integrable {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R ω.1 ω.2 < ∞)
    (hlin : Integrable (fun z => Real.exp (cavityLogFactor 0 L C (cavityRootedField n z.1) z.2))
      ((cavityRootedResidualKernel n K R ω).prod π)) :
    Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π) := by
  rw [cavity_rooted_quadratic_eq_tilted n K R ω hZ,
    cavity_tilt_prod_left _ π _ (measurable_cavityRootedQuadratic n K)] at hlin
  have hi := (integrable_tilted_iff
    ((cavity_rooted_quadratic_integrable n K R ω hZ).comp_fst π) _).mp hlin
  have he := fun z => congrArg Real.exp (cavity_rooted_exponent_split n K L C z)
  simp only [Real.exp_add] at he
  simpa only [smul_eq_mul, he] using hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial moments under the original full cavity factor.
The quadratic transformation is used only in the proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_rooted_spectral_full_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 < x i)
    (hbCascade : CascadeExponents n b) (hb : ∀ i, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hS : ∀ i, (S i).PosSemidef)
    (hΔ : ∀ i,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic (A - A₀)
        (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1))))
      (CFC.sqrt (S i))).PosDef)
    (hR : (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)).PosSemidef)
    (hQR : (cavityFactorPrecision (A - A₀)
      (CFC.sqrt (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedPriorKernel n (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S₀ P κ ν V
  have hK : K.transpose = K := by
    dsimp only [K]
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH (i : ℕ) : (H i).transpose = H i := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i),
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i)
  have hZ : ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ := by
    have hm := measurable_cavityResidualPartition n K H b
      (Matrix.isHermitian_iff_isSymm.mpr hK) hR hQR
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hm measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      (cavity_residual_partition_pos_finite n K H S b hbCascade hK hH hS hb hdet hΔ hQ
        hR hQR s).mono (fun _ h => h.2))
  have hlin := cavity_rooted_spectral_linear_moment ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
    q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C p
  let νlin := cavityRootedResidualKernel n K (H n) ×ₖ Kernel.const _ π
  let Vlin : (EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2
  have he : ∀ᵐ ω ∂P, (νlin ω).tilted Vlin = (ν ω).tilted V := by
    filter_upwards [hZ] with ω hω
    simpa only [νlin, ν, κ, Kernel.prod_apply, Kernel.const_apply, Vlin, V] using
      cavity_rooted_full_tilt_eq n K (H n) L C π ω hω
  have hmean : (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) =ᵐ[P]
      (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(νlin ω).tilted Vlin) :=
    he.mono (fun _ h => by dsimp only; rw [h])
  refine ⟨?_, hlin.2.1.congr hmean.symm, ?_⟩
  · filter_upwards [hZ, hlin.1, he] with ω hω hωlin hωeq
    refine ⟨?_, ?_⟩
    · simpa only [ν, κ, Kernel.prod_apply, Kernel.const_apply, V] using
        cavity_rooted_full_exp_integrable n K (H n) L C π ω hω
          (by simpa only [Kernel.prod_apply, Kernel.const_apply] using hωlin.1)
    · rw [← hωeq]
      exact hωlin.2
  · rw [integral_congr_ae hmean]
    exact hlin.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalFullMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full original-prior cavity moments with the precision conditions
proved for the actual diagonal base spectrum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_spectral_upper_posSemidef {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (M : ℝ)
    (hM : ∀ i, hA.eigenvalues i ≤ M) :
    (M • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  have hu : U (Matrix.diagonal hA.eigenvalues) = A := by
    simpa [U] using hA.spectral_theorem.symm
  have hc : Matrix.diagonal (fun _ : Fin d => M) = M • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have he : U (Matrix.diagonal (fun i => M - hA.eigenvalues i)) = M • 1 - A := by
    rw [show Matrix.diagonal (fun i => M - hA.eigenvalues i) =
      Matrix.diagonal (fun _ => M) - Matrix.diagonal hA.eigenvalues by
        simp only [← Matrix.diagonal_sub],
      map_sub, hc, map_smul, map_one, hu]
  have hp := (Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hM i))).mul_mul_conjTranspose_same
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  rw [← he]
  simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hp

theorem cavity_diagonal_spectral_full_moment {ι : Type*} [Fintype ι] {d k n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (e : Fin d → ℝ) (hdiag : A₀ = Matrix.diagonal e)
    (a : ι) (hemax : ∀ i, e i ≤ eig a) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 < x i) (hxmono : Antitone x)
    (hbCascade : CascadeExponents n b) (hb : ∀ i, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hS : ∀ i, (S i).PosSemidef)
    (hΔ : ∀ i,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedPriorKernel n (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  subst A₀
  have hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e := by
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hu := cavity_spectral_upper_posSemidef A hA (eig a) heig
  have hQ (i : ℕ) : (cavityFactorPrecision
      (b i • cavityBackwardQuadratic (A - Matrix.diagonal e)
        (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) hA₀ (x (i + 1))))
      (CFC.sqrt (S i))).PosDef :=
    cavity_diagonal_spectral_step_precision ρ eig hρ hsum A e hA₀ a heig₀ hemax hK hu
      (hx (i + 1)) (hxmono (Nat.le_succ i)) (hb i).le (S i) (hS i) (hΔ i)
  have hH := cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e hA₀ a heig₀ hemax (hx n)
  have hR : (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) hA₀ (x n)).PosSemidef := by
    rw [hH]
    exact Matrix.PosSemidef.diagonal (fun i => (inv_pos.mpr
      (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum (hx n)).1 a)))).le)
  have hQR := cavity_diagonal_spectral_terminal_precision ρ eig hρ hsum A e hA₀ a heig₀ hemax hK hu (hx n)
  exact cavity_rooted_spectral_full_moment ρ eig hρ hsum A (Matrix.diagonal e) hA hA₀
    a heig heig₀ q x b S hq hq0 hx hbCascade hb hgap hlast hS hΔ hQ hR hQR π L C p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

lemma finite_overlap_ae_bounds {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    ∀ᵐ s ∂pathMeasure, q 0 ≤ p s ∧ p s ≤ q (Fin.last n) := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  exact ⟨hq (Fin.zero_le _), hq (Fin.le_last _)⟩

lemma finite_overlap_deficit_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) {r : ℝ} (hr : r ≤ q (Fin.last n)) :
    0 < deficit p r := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.2)
  exact (sub_pos.mpr htop).trans_le (deficit_lower_of_ae_le p hbound hr)

theorem finite_overlap_cumulative_mass {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (j : Fin (n + 1)) :
    pathMeasure.real {s | p s ≤ q j} = cut j.succ := by
  have he : {s | p s ≤ q j} =ᵐ[pathMeasure] Iic (cut j.succ) := by
    filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
    obtain ⟨k, hk⟩ := hs
    apply propext
    change p s ≤ q j ↔ s ≤ cut j.succ
    rw [hp k s hk]
    by_cases hkj : k ≤ j
    · exact iff_of_true (hq.monotone hkj)
        (hk.2.le.trans (hcut.monotone (by simpa using hkj)))
    · have hjk : j < k := lt_of_not_ge hkj
      have hindex : j.succ ≤ k.castSucc := by
        change j.val + 1 ≤ k.val
        exact hjk
      exact iff_of_false (not_le.mpr (hq hjk))
        (not_le.mpr ((hcut.monotone hindex).trans_lt hk.1))
  have hb : cut j.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hfirst]
      exact hcut.monotone (Fin.zero_le _)
    · rw [← hlast]
      exact hcut.monotone (Fin.le_last _)
  rw [measureReal_def, measure_congr he]
  change (IsingPerceptron.unitUniform (Iic (cut j.succ))).toReal = cut j.succ
  rw [IsingPerceptron.unitUniform_Iic hb, ENNReal.toReal_ofReal hb.1]

theorem finite_overlap_value_gap {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    ∀ᵐ s ∂pathMeasure, p s ≤ q i.castSucc ∨ q i.succ ≤ p s := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  by_cases hji : j ≤ i.castSucc
  · exact Or.inl (hq hji)
  · change ¬j.val ≤ i.val at hji
    exact Or.inr (hq (by change i.val + 1 ≤ j.val; omega))

/-- The actual finite-level deficit increment, including the atoms at
both neighboring overlap values. -/
theorem finite_overlap_deficit_increment {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) {r : ℝ} (hr : r ∈ Icc (q i.castSucc) (q i.succ)) :
    deficit p r = deficit p (q i.castSucc) -
      cut i.succ.castSucc * (r - q i.castSucc) := by
  rw [deficit_affine_on_gap p
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i) hr,
    finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal ordinary residual covariance is the remaining tail of
the field-density integral; it is not an additional cascade level. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma deficit_eq_one_sub_of_ae_le (p : OverlapPath) {r : ℝ}
    (hr : ∀ᵐ s ∂pathMeasure, p s ≤ r) : deficit p r = 1 - r := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] (fun _ => 0) :=
    hr.mono (fun _ hs => max_eq_right (sub_nonpos.mpr hs))
  rw [deficit, integral_congr_ae he, integral_zero, sub_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicities in the cavity Schur determinant and the finite
spectral inverse used to evaluate the scalar cavity field. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityRepeatedSpectrum_shift_eq {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        cavityRepeatedSpectrum (n := n) (fun a => b - lam a) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavityFiniteCovariance_diagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance rho lam hrho hsum g x =
      Matrix.diagonal (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹) := by
  unfold cavityFiniteCovariance
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [he, Matrix.diagonal_mul_diagonal]
  have hg (i : Fin d) : finiteInverse rho lam hrho hsum x - lam (g i) ≠ 0 :=
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))).ne'
  simp [hg]

lemma cavityFiniteCovariance_sub_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply sub_nonneg.mpr
  exact inv_anti₀ (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum
    (hy.trans_le hyx)).1 (g i)))
    (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)

lemma cavity_finite_spectral_upper {m n : ℕ}
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ i, lam i ≤ lam a)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1) :
    (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosSemidef := by
  have hD : (lam a • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).PosSemidef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (ha _))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using
    hD.conjTranspose_mul_mul_same B

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

lemma cavityFiniteLevel_castSucc {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n i = i.castSucc := by
  apply Fin.ext
  exact min_eq_left i.isLt.le

lemma cavityFiniteLevel_succ {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n (i + 1) = i.succ := by
  apply Fin.ext
  exact min_eq_left i.isLt

lemma cavityFiniteDeficitPath_antitone {n : ℕ} (p : OverlapPath)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) : Antitone (cavityFiniteDeficitPath p q) :=
  (deficit_antitone_argument p).comp_monotone (hq.comp (cavityFiniteLevel_monotone n))

lemma cavityFiniteDeficitPath_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : ℕ) : 0 < cavityFiniteDeficitPath p q i :=
  finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop (hq (Fin.le_last _))

lemma cavityFiniteDeficitPath_step {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    cavityFiniteDeficitPath p q i - cavityFiniteDeficitPath p q (i + 1) =
      chainExponent cut i * (q i.succ - q i.castSucc) := by
  have he := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
    ⟨(hq (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut i.isLt]
  have hc : cut i.succ.castSucc = cut ⟨i + 1, by omega⟩ := congrArg cut (Fin.ext rfl)
  rw [hc] at he
  linarith

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariancePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hcut hfirst in
lemma cavityFiniteNoiseCovariance_delta (i : ℕ) :
    cavityFiniteCovariancePath rho lam hrho hsum g p q i -
      cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1) =
        chainExponent cut i • cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i := by
  rw [cavityFiniteNoiseCovariance, smul_smul,
    mul_inv_cancel₀ (finite_chainExponent_pos cut hcut hfirst i).ne', one_smul]

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullGibbs
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A total probability-kernel version of the full cavity Gibbs law.
Its fallback on a nonintegrable fiber is irrelevant on the proved full-measure set. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavityRootedFullGibbs_eq_tilted {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    cavityRootedFullGibbs n K R L C π ω =
      ((cavityRootedPriorKernel n R ω).prod π).tilted
        (fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  change normalizeMass _ = _
  simp only [Kernel.prod_apply, Kernel.const_apply]
  exact normalizeMass_exp _ _ (measurable_cavityRootedLogFactor n K L C) he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Root-retaining transport of the full cavity spin probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityAttachSpinRoot {d k : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityAttachSpinRoot (k := k) n s) := by
  exact (measurable_const.prodMk measurable_fst).prodMk measurable_snd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralDensitySquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of the matrix resolvent is its square divided by
the scalar second resolvent. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavitySpectralMatrixDensity_eq_square {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixDensity ρ eig hρ hsum A hA x =
      (1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x)) •
        (cavitySpectralMatrixPath ρ eig hρ hsum A hA x *
          cavitySpectralMatrixPath ρ eig hρ hsum A hA x) := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  change U (Matrix.diagonal _) = _ • (U (Matrix.diagonal _) * U (Matrix.diagonal _))
  rw [← map_mul, Matrix.diagonal_mul_diagonal, ← map_smul, ← Matrix.diagonal_smul]
  apply congrArg U
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.smul_apply, smul_eq_mul,
    cavityScalarResolvent_pos_eq ρ eig hρ hsum a (heig i) hx,
    one_div, pow_two, mul_inv]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralUpperEigenvalues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite compression and diagonal base obey the spectral
upper bound used by the full Gaussian moment calculation. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_eigenvalues_le_of_upper {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (M : ℝ)
    (hM : (M • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) :
    ∀ i, hA.eigenvalues i ≤ M := by
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have ha : U.transpose * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq, U] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hu : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have he : U.transpose * (M • 1 - A) * U = Matrix.diagonal (fun i => M - hA.eigenvalues i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hu, ha]
    rw [show M • (1 : Matrix (Fin d) (Fin d) ℝ) = Matrix.diagonal (fun _ => M) by
      ext i j; by_cases h : i = j <;> simp [h]]
    exact Matrix.diagonal_sub _ _
  have hp := hM.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, he] at hp
  intro i
  exact sub_nonneg.mp (by simpa only [Matrix.diagonal_apply_eq] using hp.diag_nonneg (i := i))

lemma cavity_compressed_eigenvalues_le {m N d : ℕ}
    (eig : Fin m → ℝ) (a : Fin m) (ha : ∀ j, eig j ≤ eig a)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hA : (B.transpose * cavityRepeatedSpectrum (n := N) eig * B).IsHermitian) :
    ∀ i, hA.eigenvalues i ≤ eig a :=
  cavity_eigenvalues_le_of_upper _ hA _ (cavity_finite_spectral_upper eig a ha B hB)

lemma cavity_diagonal_eigenvalues_le {m d : ℕ}
    (eig : Fin m → ℝ) (g : Fin d → Fin m) (a : Fin m) (ha : ∀ j, eig j ≤ eig a)
    (hA : (Matrix.diagonal (fun j => eig (g j))).IsHermitian) :
    ∀ i, hA.eigenvalues i ≤ eig a := by
  apply cavity_eigenvalues_le_of_upper _ hA
  have he : eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun j => eig (g j)) =
      Matrix.diagonal (fun j => eig a - eig (g j)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (ha (g j)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteOriginalMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full tilted radial moments for the actual finite spectral cavity law,
with the spectral upper bounds and covariance identities discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_original_moment {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let H := cavityFiniteCovariancePath ρ eig hρ hsum g p q
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
        (cavityGaussianMarks S) : Measure _)
    let ν := fun ω => (cavityRootedPriorKernel n (H n) ω).prod π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^ℓ) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^ℓ ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^ℓ ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S S₀ P ν V
  let A := B.transpose * cavityRepeatedSpectrum (n := N) eig * B
  let A₀ := Matrix.diagonal (fun i => eig (g i))
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change A.transpose = A
    dsimp only [A, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hA₀ : A₀.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    exact Matrix.diagonal_transpose _
  have heig := cavity_compressed_eigenvalues_le eig a ha B hB hA
  have heig₀ := cavity_diagonal_eigenvalues_le eig g a ha hA₀
  let x := cavityFiniteDeficitPath p q
  let q' := fun i => q (cavityFiniteLevel n i)
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hpath (i : ℕ) : cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) = H i := by
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i)]
    rfl
  have hdensity : q' 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0) = S₀ := by
    rw [cavitySpectralMatrixDensity_eq_square ρ eig hρ hsum A₀ hA₀ a heig₀ (hx 0), hpath]
    simp only [q', cavityFiniteLevel_zero]
    rfl
  have hgap (i : ℕ) (hi : i < n) : x i - x (i + 1) =
      chainExponent cut i * (q' (i + 1) - q' i) := by
    have h0 : cavityFiniteLevel n i = (⟨i,hi⟩ : Fin n).castSucc := cavityFiniteLevel_castSucc ⟨i,hi⟩
    have h1 : cavityFiniteLevel n (i + 1) = (⟨i,hi⟩ : Fin n).succ := cavityFiniteLevel_succ ⟨i,hi⟩
    simpa only [x, q', h0, h1] using
      cavityFiniteDeficitPath_step p cut hcut hfirst hlast q hq hp ⟨i,hi⟩
  have ht : x n = 1 - q' n := by
    simp only [x, cavityFiniteDeficitPath, q', cavityFiniteLevel_last]
    exact deficit_eq_one_sub_of_ae_le p
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop i
  have hΔ (i : ℕ) : cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = chainExponent cut i • S i := by
    rw [hpath, hpath]
    exact cavityFiniteNoiseCovariance_delta ρ eig hρ hsum g p cut hcut hfirst q i
  have hm := cavity_diagonal_spectral_full_moment ρ eig hρ hsum A A₀ hA hA₀
    (fun i => eig (g i)) rfl a (fun i => ha (g i)) heig heig₀ q' x (chainExponent cut) S
    (hq.monotone.comp (cavityFiniteLevel_monotone n))
    (by simpa only [q', cavityFiniteLevel_zero] using
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1)
    hx (cavityFiniteDeficitPath_antitone p q hq.monotone)
    (chainExponent_admissible hcut hfirst hlast) (finite_chainExponent_pos cut hcut hfirst)
    hgap ht hS hΔ π L C ℓ
  simpa only [hpath, hdensity, Kernel.prod_apply, Kernel.const_apply] using hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianForestLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite restrictions of the independent Gaussian forest, and the
literal sum of its marks along a labeled cavity leaf. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavity_labeled_leaf_sum {d : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) (v : LabeledLeaf n)
    (s : EuclideanSpace ℝ (Fin d)) :
    cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) v) =
      s + ∑ i : Fin n, g (edgeAt n v i) := by
  rw [cavityLeafSum_eq_mark_sum]
  simp_rw [noiseLeafMark_labeled]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled representation of the full cavity spin law and its field projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal NNReal

namespace InvariantIsing

lemma measurable_cavityLabeledSpinMap {d k : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityLabeledSpinMap (k := k) n T g) := by
  exact (((measurable_of_countable (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g))).comp
    measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledRoot
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled coordinates for the actual rooted full Gibbs kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

lemma cavity_labeled_spin_prior_law {d k : ℕ} (n : ℕ)
    (T : LabeledTree n) (g : ForestVertex n → EuclideanSpace ℝ (Fin d))
    (hgood : GoodNoiseTree _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)))
    (ht : 0 < noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) ∧
      noiseTreeTotal _ n (labeledNoiseJoin _ n (T, markForestOfCoords _ n g)) < ∞)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    MeasurePreserving (cavityLabeledSpinMap n T g)
      (((labeledLeafLaw n T).prod (multivariateGaussian 0 R)).prod π)
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (labeledNoiseJoin _ n (T, markForestOfCoords _ n g))).prod
          (multivariateGaussian 0 R)).prod π) := by
  have hp : MeasurePreserving
      (labeledNoiseLeaf (EuclideanSpace ℝ (Fin d)) n (T, markForestOfCoords _ n g))
      (labeledLeafLaw n T)
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (labeledNoiseJoin _ n (T, markForestOfCoords _ n g))) :=
    ⟨measurable_of_countable _, labeledLeafLaw_noiseMap _ n T _ hgood ht⟩
  exact (hp.prod (MeasurePreserving.id (multivariateGaussian 0 R))).prod
    (MeasurePreserving.id π)

lemma cavity_attach_spin_root_prior_law {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    MeasurePreserving (cavityAttachSpinRoot n s)
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
        (multivariateGaussian 0 R)).prod π)
      ((cavityRootedPriorKernel n R (s, V)).prod π) := by
  refine ⟨measurable_cavityAttachSpinRoot n s, ?_⟩
  rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  change (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π).map
      (Prod.map (Prod.mk s) (id : Spin k → Spin k)) = _
  simpa only [Measure.map_id, id_eq] using (Measure.map_prod_map
    ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
    (measurable_const.prodMk measurable_id) measurable_id).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledDisorderLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The independent labeled coordinates give the original common-root
noise-cascade disorder law exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

theorem cavity_labeled_noise_disorder_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    MeasurePreserving (cavityLabeledNoiseDisorderMap n)
      (cavityLabeledDisorderLaw n b S₀ S)
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) := by
  let PT := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let PS := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀
  let PG := Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))
  have hnoise : MeasurePreserving
      (fun p : LabeledTree n × (ForestVertex n → EuclideanSpace ℝ (Fin d)) =>
        labeledNoiseJoin _ n (p.1, markForestOfCoords _ n p.2))
      (PT.prod PG)
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _) :=
    ⟨by fun_prop, labeledNoiseCoordinates_law _ n b (cavityGaussianMarks S)⟩
  have h1 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc PT PS PG)
  have h2 := (Measure.measurePreserving_swap (μ := PT) (ν := PS)).prod (MeasurePreserving.id PG)
  have h3 := measurePreserving_prodAssoc PS PT PG
  have h4 := (MeasurePreserving.id PS).prod hnoise
  exact h4.comp (h3.comp (h2.comp h1))

lemma cavity_labeled_disorder_good {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hb : CascadeExponents n b) :
    ∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      (0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
        noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞) := by
  have hnoise := (noiseCascade_good (EuclideanSpace ℝ (Fin d)) n b hb
      (cavityGaussianMarks S)).and
    (cavity_noiseTreeTotal_pos_finite n b hb (cavityGaussianMarks S))
  let Q := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
    (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
  have hsnd : MeasurePreserving Prod.snd
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod Q) Q :=
    measurePreserving_snd
  have hp := hsnd.quasiMeasurePreserving.ae hnoise
  exact (cavity_labeled_noise_disorder_law n b S₀ S).quasiMeasurePreserving.ae hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledPriorTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-state finite model prior and potential are exactly the
labeled realization of the original common-root cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

lemma measurable_cavityLabeledRootMap {d k : ℕ} (n : ℕ)
    (ω : CavityLabeledDisorder d n) :
    Measurable (cavityLabeledRootMap (k := k) n ω) :=
  (measurable_cavityAttachSpinRoot n ω.2.1).comp
    (measurable_cavityLabeledSpinMap n ω.1 ω.2.2)

lemma cavityLabeledRootMap_potential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (ω : CavityLabeledDisorder d n)
    (x : CavityLabeledState d k n) :
    cavityLogFactor K L C (cavityRootedField n (cavityLabeledRootMap n ω x).1)
      (cavityLabeledRootMap n ω x).2 = cavityLabeledPotential n K L C (ω,x) := by
  simp only [cavityLabeledRootMap, Function.comp_apply, cavityAttachSpinRoot,
    cavityLabeledSpinMap, cavityRootedField, cavity_labeled_leaf_sum,
    cavityLabeledPotential, cavityLabeledEndpoint, cavityLabeledField]

lemma cavity_labeled_model_prior_law {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞) :
    MeasurePreserving (cavityLabeledRootMap n ω) (cavityLabeledPriorKernel n R π ω)
      ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π) := by
  rw [cavityLabeledPriorKernel_apply]
  exact (cavity_attach_spin_root_prior_law n R ω.2.1 _ π).comp
    (cavity_labeled_spin_prior_law n ω.1 ω.2.2 hg ht R π)

lemma cavity_labeled_model_exp_integrable {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞)
    (hI : Integrable (fun z => Real.exp
      (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π)) :
    Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (cavityLabeledPriorKernel n R π ω) := by
  have hi := (cavity_labeled_model_prior_law n R π ω hg ht).integrable_comp_of_integrable hI
  simpa only [Function.comp_def, cavityLabeledRootMap_potential] using hi

lemma cavity_labeled_model_tilted_law {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n)
    (hg : GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2)
    (ht : 0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞)
    (hI : Integrable (fun z => Real.exp
      (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n R (cavityLabeledNoiseDisorderMap n ω)).prod π)) :
    ((cavityLabeledPriorKernel n R π ω).tilted
      (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω) =
      cavityRootedFullGibbs n K R L C π (cavityLabeledNoiseDisorderMap n ω) := by
  have hp := cavity_labeled_model_prior_law n R π ω hg ht
  rw [cavityRootedFullGibbs_eq_tilted n K R L C π _ hI]
  let V : CavitySpinState d k n → ℝ := fun z =>
    cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have hV : Measurable V := measurable_cavityRootedLogFactor n K L C
  have he : (fun x => cavityLabeledPotential n K L C (ω,x)) = V ∘ cavityLabeledRootMap n ω :=
    funext fun x => (cavityLabeledRootMap_potential n K L C ω x).symm
  rw [he, cavity_tilt_map _ _ hp.measurable V hV, hp.map_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledTiltMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of full tilted radial moments to the fixed-state labeled
cavity model used in the normalized replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityLabeledRootMap_field {d k : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n)
    (x : CavityLabeledState d k n) :
    cavityRootedField n (cavityLabeledRootMap n ω x).1 = (cavityLabeledEndpoint n (ω,x)).1 := by
  simp only [cavityLabeledRootMap, Function.comp_apply, cavityAttachSpinRoot,
    cavityLabeledSpinMap, cavityRootedField, cavity_labeled_leaf_sum,
    cavityLabeledEndpoint, cavityLabeledField]

theorem cavity_labeled_tilted_radial_moment {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ℓ : ℕ) {M : ℝ}
    (hI : ∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      Integrable (fun x => Real.exp (cavityLogFactor K L C (cavityRootedField n x.1) x.2))
        ((cavityRootedPriorKernel n R ω).prod π))
    (hMom : (∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      Integrable (fun x => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2))) ∧
      Integrable (fun ω => ∫ x, ‖cavityRootedField n x.1‖^ℓ
        ∂((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2))
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) ∧
      (∫ ω, ∫ x, ‖cavityRootedField n x.1‖^ℓ
        ∂((cavityRootedPriorKernel n R ω).prod π).tilted
          (fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) ≤ M) :
    (∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))
      (cavityLabeledDisorderLaw n b S₀ S) ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))
      ∂cavityLabeledDisorderLaw n b S₀ S) ≤ M := by
  let V : CavitySpinState d k n → ℝ := fun x => cavityLogFactor K L C (cavityRootedField n x.1) x.2
  let J := fun ω => ∫ x, ‖cavityRootedField n x.1‖^ℓ
    ∂((cavityRootedPriorKernel n R ω).prod π).tilted V
  let f := cavityLabeledNoiseDisorderMap (d := d) n
  let P := cavityLabeledDisorderLaw n b S₀ S
  let A := fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
    ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))
  have hmap := cavity_labeled_noise_disorder_law n b S₀ S
  have hgood := cavity_labeled_disorder_good n b S₀ S hb
  have hpulled := hmap.quasiMeasurePreserving.ae (hI.and hMom.1)
  have hpoint : ∀ᵐ ω ∂P,
      Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) ∧
      A ω = J (f ω) := by
    filter_upwards [hpulled, hgood] with ω hω hg
    have heI := cavity_labeled_model_exp_integrable n K R L C π ω hg.1 hg.2 hω.1
    have hm := cavity_labeled_model_tilted_law n K R L C π ω hg.1 hg.2 hω.1
    rw [cavityRootedFullGibbs_eq_tilted n K R L C π _ hω.1] at hm
    have hi : Integrable (fun x : CavitySpinState d k n => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityLabeledPriorKernel n R π ω).tilted
          (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω)) := by
      rw [hm]
      exact hω.2
    have hInt := (integrable_map_measure hi.aestronglyMeasurable
      (measurable_cavityLabeledRootMap n ω).aemeasurable).mp hi
    have hEq := integral_map (measurable_cavityLabeledRootMap n ω).aemeasurable
      (show AEStronglyMeasurable (fun x : CavitySpinState d k n => ‖cavityRootedField n x.1‖^ℓ)
        (((cavityLabeledPriorKernel n R π ω).tilted
          (fun x => cavityLabeledPotential n K L C (ω,x))).map (cavityLabeledRootMap n ω)) from
        hi.aestronglyMeasurable)
    simp only [Function.comp_def, cavityLabeledRootMap_field] at hInt hEq
    refine ⟨heI, hInt, ?_⟩
    change _ = A ω at hEq
    rw [hm] at hEq
    exact hEq.symm
  have hj := hmap.integrable_comp_of_integrable hMom.2.1
  have ha : A =ᵐ[P] J ∘ f := hpoint.mono (fun _ h => h.2.2)
  refine ⟨hpoint.mono (fun _ h => ⟨h.1,h.2.1⟩), hj.congr ha.symm, ?_⟩
  rw [integral_congr_ae ha]
  exact (hmap.hasLaw.integral_comp hMom.2.1.aestronglyMeasurable).le.trans hMom.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteLabeledMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full tilted moments in the literal finite labeled model, with
all geometric and spectral hypotheses specialized to the cavity data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_labeled_moment_oai {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) P ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)) ∂P) ≤
      cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K R S S₀ P
  have hm := cavity_finite_original_moment ρ eig hρ hsum B hB g a ha p cut hcut hfirst hlast
    q hq hp htop L C π ℓ
  exact cavity_labeled_tilted_radial_moment n (chainExponent cut)
    (chainExponent_admissible hcut hfirst hlast) S₀ R S K L C π ℓ
    (hm.1.mono fun _ h => h.1) ⟨hm.1.mono (fun _ h => h.2), hm.2⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_finite_labeled_moment_oai := @OAI.InvariantIsing.cavity_finite_labeled_moment_oai
