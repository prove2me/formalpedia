-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_full_depth_test_evaluation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:01.239117+00:00
-- url     : https://prove2.me/submissions/23c488a9-41d2-4694-80bd-99da5eac9a6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
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
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_linear_rooted_depth_evaluation
import Theorems.Thm_OAI_InvariantIsing_cavity_rooted_depth_test_transport

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `ProbabilityTheory.charFun_map_eq_charFun_map_inner_one` (InvariantIsing CavityPrecisionTiltLaw, q251). -/
theorem _root_.ProbabilityTheory.charFun_map_eq_charFun_map_inner_one {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure Ω} {Y : Ω → E} (hY : AEMeasurable Y μ) (t : E) :
    MeasureTheory.charFun (μ.map Y) t = MeasureTheory.charFun (μ.map fun ω => inner ℝ (Y ω) t) 1 := by
  have h2 : AEMeasurable (fun ω => inner ℝ (Y ω) t) μ := by fun_prop
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map hY (by fun_prop), MeasureTheory.integral_map h2 (by fun_prop)]
  simp
end OAICompat434

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

theorem cavity_quadratic_det_ratio {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    (1 - (P - C) * cavityBackwardQuadratic K C).det =
      (1 - P * K).det / (1 - C * K).det := by
  apply (eq_div_iff hC.ne_zero).2
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  rw [mul_assoc, Matrix.det_nonsing_inv_mul_det _ hC, mul_one]

theorem cavityStepTransition_eq {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityStepTransition K P C = (1 - C * K) * (1 - P * K)⁻¹ := by
  unfold cavityStepTransition
  apply Matrix.inv_eq_right_inv
  rw [cavity_quadratic_factor K P C hC]
  calc
    ((1 - P * K) * (1 - C * K)⁻¹) *
        ((1 - C * K) * (1 - P * K)⁻¹) =
        (1 - P * K) * ((1 - C * K)⁻¹ * (1 - C * K)) * (1 - P * K)⁻¹ := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hC, mul_one, Matrix.mul_nonsing_inv _ hP]

/-- The identity `J_i T_i = J_{i-1}` used in square completion. -/
theorem cavity_quadratic_backward_inverse {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * cavityStepTransition K P C = (1 - P * K)⁻¹ := by
  rw [cavityStepTransition_eq K P C hP hC, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hC, one_mul]

/-- The backward coefficient after integrating one level is exactly
`K_{i-1}`; this is the matrix identity in `cav:q-gaussian-integral`. -/
theorem cavityBackwardQuadratic_step {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityBackwardQuadratic K C * cavityStepTransition K P C =
      cavityBackwardQuadratic K P := by
  unfold cavityBackwardQuadratic
  rw [mul_assoc, cavity_quadratic_backward_inverse K P C hP hC]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Gaussian images, used for finitely many replica
projections of a fresh frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_rectangular_adjoint {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (B : Matrix a b ℝ) :
    B.toEuclideanLin.toContinuousLinearMap.adjoint =
      B.transpose.toEuclideanLin.toContinuousLinearMap := by
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianAffineImage
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square affine image needed after standard-Gaussian square completion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_multivariateGaussian_affine_image {d : ℕ}
    (B S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (m u : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian m S).map (fun z => u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z) =
      multivariateGaussian (u + Matrix.toEuclideanCLM (𝕜 := ℝ) B m)
        (B * S * B.transpose) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hp : (B * S * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same B
  have he : (fun z => u + L z) = (fun z => u + z) ∘ L := rfl
  change (multivariateGaussian m S).map (fun z => u + L z) = _
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop)]
    change (∫ z, u + z ∂(multivariateGaussian m S).map L) = _
    have hsplit := integral_add (f := fun _ : EuclideanSpace ℝ (Fin d) => u)
      (g := fun z : EuclideanSpace ℝ (Fin d) => z)
      (μ := (multivariateGaussian m S).map L) (integrable_const _) IsGaussian.integrable_id
    rw [hsplit, integral_const,
      L.integral_id_map IsGaussian.integrable_id]
    simp only [probReal_univ, one_smul, integral_id_multivariateGaussian,
      integral_id_multivariateGaussian']
    rfl
  · rw [covarianceBilin_map_const_add]
    ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id L,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hp]
    rw [← Matrix.inner_toEuclideanCLM S, ContinuousLinearMap.adjoint_inner_left]
    have hL : L.adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) B.transpose :=
      cavity_rectangular_adjoint B
    rw [hL, ← Matrix.inner_toEuclideanCLM (B * S * B.transpose)]
    simp only [map_mul, mul_apply_eq_comp]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultivariateGaussian
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive covariance of a quadratic Gaussian tilt. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_inverse_push_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    (1 - (B * B.transpose) * K)⁻¹ * B = B * (cavityFactorPrecision K B)⁻¹ := by
  have hA : IsUnit (1 - (B * B.transpose) * K).det := by
    rwa [← cavity_factor_det]
  have hf : (1 - (B * B.transpose) * K) * B = B * cavityFactorPrecision K B := by
    unfold cavityFactorPrecision
    noncomm_ring
  have hc : (1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹) = B := by
    rw [← mul_assoc, hf, mul_assoc, Matrix.mul_nonsing_inv _ hQ, mul_one]
  calc
    _ = (1 - (B * B.transpose) * K)⁻¹ *
        ((1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹)) := by rw [hc]
    _ = _ := Matrix.nonsing_inv_mul_cancel_left _ _ hA

theorem cavity_tilt_covariance_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    cavityResolvent K (B * B.transpose) =
      B * (cavityFactorPrecision K B)⁻¹ * B.transpose := by
  unfold cavityResolvent
  rw [← mul_assoc, cavity_inverse_push_factor K B hQ]

theorem cavity_tilt_covariance_posSemidef {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef) :
    (cavityResolvent K S).PosSemidef := by
  rw [← cavity_covariance_sqrt_factor S hS,
    cavity_tilt_covariance_factor K (CFC.sqrt S) (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.inv.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt S)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionTiltMoments
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laplace transforms of the positive-precision quadratic Gaussian tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_precision_potential_integrable {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => Real.exp (cavityPrecisionPotential Q l z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  cavity_gaussian_precision_integrable Q hQ l

lemma cavity_precision_potential_integral {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    (∫ z, Real.exp (cavityPrecisionPotential Q l z)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt Q.det)⁻¹ *
        Real.exp (⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ / 2) :=
  cavity_gaussian_precision_integral Q hQ l

lemma cavity_precision_inverse_square {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    (⟪l + t • v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ (l + t • v)⟫ -
      ⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫) / 2 =
      t * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ +
        t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫ := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ.inv.isHermitian l v
  change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l, v⟫ =
    ⟪l, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫ at hs
  have hc := real_inner_comm v (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l)
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [← hs, hc]
  ring

theorem cavity_precision_tilt_mgf {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mgf (fun z => ⟪v, z⟫)
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).tilted (cavityPrecisionPotential Q l)) t =
      Real.exp (t * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l⟫ +
        t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ v⟫) := by
  rw [mgf, integral_exp_tilted]
  have he : cavityPrecisionPotential Q l + (fun z => t * ⟪v, z⟫) =
      cavityPrecisionPotential Q (l + t • v) := by
    funext z
    simp only [cavityPrecisionPotential, Pi.add_apply, inner_add_left, real_inner_smul_left]
    ring
  rw [he, cavity_precision_potential_integral Q hQ,
    cavity_precision_potential_integral Q hQ]
  have hn : (Real.sqrt Q.det)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hQ.det_pos).ne'
  rw [mul_div_mul_left _ _ hn, ← Real.exp_sub]
  congr 1
  rw [← sub_div, cavity_precision_inverse_square Q hQ]

theorem cavity_multivariate_gaussian_mgf {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (m v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mgf (fun z => ⟪v, z⟫) (multivariateGaussian m S) t =
      Real.exp (t * ⟪v, m⟫ + t ^ 2 / 2 * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ v
  have hm : (∫ z, L z ∂multivariateGaussian m S) = ⟪v, m⟫ := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_multivariateGaussian]
    rfl
  have hv : Var[L; multivariateGaussian m S] =
      ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫ := by
    change Var[fun z => ⟪v, z⟫; multivariateGaussian m S] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id v,
      covarianceBilin_multivariateGaussian hS, Matrix.inner_toEuclideanCLM]
  have hLaw : HasLaw L (gaussianReal ⟪v, m⟫
      (⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫).toNNReal) (multivariateGaussian m S) := by
    refine ⟨L.measurable.aemeasurable, ?_⟩
    rw [IsGaussian.map_eq_gaussianReal, hm, hv]
  have hp : 0 ≤ ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫ := by
    rw [← hv]
    exact variance_nonneg _ _
  calc
    _ = Real.exp (⟪v, m⟫ * t +
        (⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫).toNNReal * t ^ 2 / 2) :=
      mgf_gaussianReal hLaw.map_eq t
    _ = _ := by
      rw [Real.coe_toNNReal _ hp]
      congr 1
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionTiltLaw
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the full Gaussian law under a quadratic tilt.
The proof uses the already computed Laplace transforms, so it does not
require a density with respect to Lebesgue measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

private lemma cavity_charFun_projection {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin d)) :
    charFun μ v = charFun (μ.map (fun z => ⟪v, z⟫)) 1 := by
  have he : (fun z : EuclideanSpace ℝ (Fin d) => ⟪z, v⟫) = (fun z => ⟪v, z⟫) :=
    funext fun z => real_inner_comm _ _
  have h := charFun_map_eq_charFun_map_inner_one (μ := μ) (Y := id) aemeasurable_id v
  simpa only [Measure.map_id, id_eq, he] using h

private lemma cavity_law_eq_of_projection_mgf {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmgf : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      mgf (fun z => ⟪v, z⟫) μ t = mgf (fun z => ⟪v, z⟫) ν t)
    (hpos : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), 0 < mgf (fun z => ⟪v, z⟫) μ t) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext v
  let X : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ⟪v, z⟫
  have hm : mgf X μ = mgf X ν := funext (hmgf v)
  have hd : integrableExpSet X μ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    change Integrable (fun z => Real.exp (t * X z)) μ
    exact mgf_pos_iff.mp (hpos v t)
  have hc := eqOn_complexMGF_of_mgf hm
    (show Complex.I ∈ {z : ℂ | z.re ∈ interior (integrableExpSet X μ)} from
      by simp only [Set.mem_ofPred_eq, hd, interior_univ, Set.mem_univ])
  rw [cavity_charFun_projection μ v, cavity_charFun_projection ν v]
  rw [← complexMGF_mul_I (μ := μ) (X := X) (by fun_prop) 1,
    ← complexMGF_mul_I (μ := ν) (X := X) (by fun_prop) 1]
  simpa only [Complex.ofReal_one, one_mul] using hc

/-- The normalized quadratic tilt of a standard Gaussian has the full
Gaussian law with mean `Q⁻¹l` and covariance `Q⁻¹`. -/
theorem cavity_precision_tilt_law {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).tilted (cavityPrecisionPotential Q l) =
      multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l) Q⁻¹ := by
  have := isProbabilityMeasure_tilted (cavity_precision_potential_integrable Q hQ l)
  apply cavity_law_eq_of_projection_mgf
  · intro v t
    rw [cavity_precision_tilt_mgf Q hQ, cavity_multivariate_gaussian_mgf Q⁻¹ hQ.inv.posSemidef]
  · intro v t
    rw [cavity_precision_tilt_mgf Q hQ]
    exact Real.exp_pos _

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

lemma cavity_tilt_add_const {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Integrable (fun z => Real.exp (f z)) μ) (c : ℝ) :
    μ.tilted (fun z => f z + c) = μ.tilted f := by
  have := isProbabilityMeasure_tilted hf
  have he : (f + fun _ : EuclideanSpace ℝ (Fin d) => c) = (fun z => f z + c) := by
    funext z
    rfl
  rw [← he]
  exact (tilted_tilted hf (fun _ : EuclideanSpace ℝ (Fin d) => c)).symm.trans
    (tilted_const (μ.tilted f) c)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianTiltLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete conditional Gaussian kernel in `cav:q-kernels`,
including degenerate covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_gaussian_quadratic_tilt_law {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (multivariateGaussian u S).tilted
      (fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) =
      multivariateGaussian
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u)
        (cavityResolvent K S) := by
  let B := CFC.sqrt S
  let Q := cavityFactorPrecision K B
  let l := cavityFactorLinear K B u
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z => u + Matrix.toEuclideanCLM (𝕜 := ℝ) B z
  let f : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2
  have hB : B * B.transpose = S := cavity_covariance_sqrt_factor S hS
  have hQdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hf : f ∘ F = fun z => cavityPrecisionPotential Q l z +
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) K u⟫ / 2 := by
    funext z
    exact cavity_factor_exponent K B hK u z
  have hbase : multivariateGaussian u S =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map F := rfl
  have hmean : u + Matrix.toEuclideanCLM (𝕜 := ℝ) B
      (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u := by
    have hi := cavity_covariance_inverse K B hQdet
    rw [hB] at hi
    rw [hi]
    simp only [map_add, map_one, map_mul, add_apply, one_apply_eq_self,
      mul_apply_eq_comp, l, cavityFactorLinear, Q]
  have hcov : B * Q⁻¹ * B.transpose = cavityResolvent K S := by
    have hi := cavity_tilt_covariance_factor K B hQdet
    rw [hB] at hi
    exact hi.symm
  change (multivariateGaussian u S).tilted f = _
  rw [hbase, ← cavity_tilt_map _ F (by fun_prop) f (by fun_prop), hf,
    cavity_tilt_add_const _ (cavityPrecisionPotential Q l)
      (cavity_precision_potential_integrable Q hQ l),
    cavity_precision_tilt_law Q hQ l,
    cavity_multivariateGaussian_affine_image B Q⁻¹ hQ.inv.posSemidef _ u,
    hmean, hcov]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma abs_integral_le_const_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : |∫ ω, F ω ∂μ| ≤ c := by
  calc
    _ ≤ ∫ ω, |F ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂μ := integral_mono ((integrable_of_measurable_abs_le hF hbound).abs)
      (integrable_const _) hbound
    _ = c := by simp

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRecursion
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma cavity_scaled_backward_step {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    cavityBackwardQuadratic (ζ • cavityBackwardQuadratic K C) S =
      ζ • cavityBackwardQuadratic K P := by
  have he : S * (ζ • cavityBackwardQuadratic K C) =
      (P - C) * cavityBackwardQuadratic K C := by
    rw [hΔ, Matrix.mul_smul, Matrix.smul_mul]
  change (ζ • cavityBackwardQuadratic K C) *
      (1 - S * (ζ • cavityBackwardQuadratic K C))⁻¹ =
    ζ • cavityBackwardQuadratic K P
  rw [he, Matrix.smul_mul]
  exact congrArg (fun M => ζ • M) (cavityBackwardQuadratic_step K P C hP hC)

lemma cavity_scaled_step_determinant {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hC : IsUnit (1 - C * K).det) (hΔ : P - C = ζ • S) :
    (1 - S * (ζ • cavityBackwardQuadratic K C)).det =
      (1 - P * K).det / (1 - C * K).det := by
  have he : S * (ζ • cavityBackwardQuadratic K C) =
      (P - C) * cavityBackwardQuadratic K C := by
    rw [hΔ, Matrix.mul_smul, Matrix.smul_mul]
  rw [he]
  exact cavity_quadratic_det_ratio K P C hC

/-- The single backward Gaussian step `cav:q-gaussian-integral`.
The precision hypothesis is supplied by `cavity_scaled_step_precision`
for the manuscript's diagonal covariance path. -/
theorem cavity_gaussian_recursive_logIntegral {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hC : C.transpose = C) (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    (1 / ζ) * Real.log (∫ z : EuclideanSpace ℝ (Fin d),
      Real.exp (ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫)
      ∂multivariateGaussian 0 S) =
      -(1 / (2 * ζ)) * Real.log ((1 - P * K).det / (1 - C * K).det) +
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K P) u⟫ / 2 := by
  have hL : (cavityBackwardQuadratic K C).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (cavityBackwardQuadratic_transpose K C hK hC hCdet)
  have hζL : (ζ • cavityBackwardQuadratic K C).IsHermitian := hL.smul (IsSelfAdjoint.all ζ)
  have he (z : EuclideanSpace ℝ (Fin d)) :
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (ζ • cavityBackwardQuadratic K C) (u + z)⟫ / 2 =
      ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫ := by
    simp only [map_smul, smul_apply, real_inner_smul_right]
    ring
  have h := cavity_multivariate_gaussian_logIntegral
    (ζ • cavityBackwardQuadratic K C) S hζL hS hQ u
  simp_rw [he] at h
  rw [cavity_scaled_step_determinant K P C S ζ hCdet hΔ,
    cavity_scaled_backward_step K P C S ζ hPdet hCdet hΔ] at h
  simp only [map_smul, smul_apply, real_inner_smul_right] at h
  rw [h]
  field_simp [hζ.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix covariance identities of `cav:q-innovations`.  These
identities apply also to zero covariance increments. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- Rescaling a tilted-step covariance by `J_i` gives the innovation
covariance with the previous inverse on the left. -/
theorem cavity_rescaled_step_covariance {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * (cavityStepTransition K P C * S) *
        ((1 - C * K)⁻¹).transpose =
      (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose := by
  rw [← mul_assoc, cavity_quadratic_backward_inverse K P C hP hC]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianInnovation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered innovation of a retained quadratic Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_shifted_gaussian_quadratic_tilt_law {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).tilted
      (fun z => ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫ / 2)).map
        (fun z => u + z) =
      multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - S * K)⁻¹ u)
        (cavityResolvent K S) := by
  have hbase : (multivariateGaussian 0 S).map (fun z => u + z) =
      multivariateGaussian u S := by
    simpa only [map_one, one_apply_eq_self, map_zero, add_zero, one_mul, mul_one,
      Matrix.transpose_one] using
      cavity_multivariateGaussian_affine_image (1 : Matrix (Fin d) (Fin d) ℝ) S hS 0 u
  have ht := cavity_tilt_map (multivariateGaussian 0 S) (fun z => u + z) (by fun_prop)
    (fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) (by fun_prop)
  change ((multivariateGaussian 0 S).tilted
    ((fun y => ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) K y⟫ / 2) ∘ (fun z => u + z))).map
      (fun z => u + z) = _
  rw [ht, hbase]
  exact cavity_gaussian_quadratic_tilt_law K S hK hS hQ u

/-- Under the retained quadratic weight, the rescaled increment has
an ancestor-independent centered Gaussian law. -/
theorem cavity_gaussian_step_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).tilted
      (fun z => ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫)).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  let L := ζ • cavityBackwardQuadratic K C
  let J := (1 - C * K)⁻¹
  let T := cavityStepTransition K P C
  have hL : L.IsHermitian :=
    (Matrix.isHermitian_iff_isSymm.mpr
      (cavityBackwardQuadratic_transpose K C hK hC hCdet)).smul (IsSelfAdjoint.all ζ)
  have hLT : (1 - S * L)⁻¹ = T := by
    dsimp [L, T, cavityStepTransition]
    rw [hΔ, Matrix.smul_mul, Matrix.mul_smul]
  have hLS : cavityResolvent L S = T * S := by
    rw [cavityResolvent, hLT]
  have hcov : (T * S).PosSemidef := by
    rw [← hLS]
    exact cavity_tilt_covariance_posSemidef L S hS hQ
  have hpot : (fun z : EuclideanSpace ℝ (Fin d) =>
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) L (u + z)⟫ / 2) =
      (fun z => ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫) := by
    funext z
    simp only [L, map_smul, smul_apply, real_inner_smul_right]
    ring
  have hshift := cavity_shifted_gaussian_quadratic_tilt_law L S hL hS hQ u
  rw [hpot, hLT, hLS] at hshift
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => u + z
  let G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y =>
    -Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u +
      Matrix.toEuclideanCLM (𝕜 := ℝ) J y
  have hmean : -Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u +
      Matrix.toEuclideanCLM (𝕜 := ℝ) J (Matrix.toEuclideanCLM (𝕜 := ℝ) T u) = 0 := by
    rw [← mul_apply_eq_comp, ← map_mul,
      cavity_quadratic_backward_inverse K P C hPdet hCdet, neg_add_cancel]
  have hJcov : J * (T * S) * J.transpose =
      (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose :=
    cavity_rescaled_step_covariance K P C S hPdet hCdet
  have hfun : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) J (u + z) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) = G ∘ F := by
    funext z
    dsimp [G, F]
    abel
  change Measure.map _ _ = _
  rw [hfun, ← Measure.map_map (by fun_prop : Measurable G) (by fun_prop : Measurable F),
    hshift, cavity_multivariateGaussian_affine_image J (T * S) hcov _
      (-Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u), hmean, hJcov]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedWeight
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized fractional weights for the quadratic retained marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_retained_weight_density {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ)
    (hf : Integrable (fun z => Real.exp (f z)) μ) (b : ℝ) (hb : b ≠ 0) :
    μ.withDensity (fun z => ENNReal.ofReal
      (Real.exp ((f z - Real.log (∫ x, Real.exp (f x) ∂μ)) / b) ^ b)) =
      μ.tilted f := by
  unfold Measure.tilted
  congr 1
  funext z
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, div_mul_cancel₀ _ hb,
    Real.exp_sub, Real.exp_log (integral_exp_pos hf)]

/-- The fractional density used in the retained tree is exactly the
normalized quadratic tilt, with no ordinary terminal exponential
moment required. -/
theorem cavity_retained_gaussian_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : ζ ≠ 0)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    let f := fun z : EuclideanSpace ℝ (Fin d) =>
      ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫
    ((multivariateGaussian 0 S).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp ((f z - Real.log (∫ x, Real.exp (f x)
          ∂multivariateGaussian 0 S)) / ζ) ^ ζ))).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  dsimp only
  have hL : (cavityBackwardQuadratic K C).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (cavityBackwardQuadratic_transpose K C hK hC hCdet)
  have hζL : (ζ • cavityBackwardQuadratic K C).IsHermitian := hL.smul (IsSelfAdjoint.all ζ)
  have he (z : EuclideanSpace ℝ (Fin d)) :
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (ζ • cavityBackwardQuadratic K C) (u + z)⟫ / 2 =
      ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫ := by
    simp only [map_smul, smul_apply, real_inner_smul_right]
    ring
  have hf := cavity_multivariate_gaussian_integrable
    (ζ • cavityBackwardQuadratic K C) S hζL hQ u
  simp_rw [he] at hf
  rw [cavity_retained_weight_density _ _ hf ζ hζ]
  exact cavity_gaussian_step_innovation_law K P C S hK hC hS ζ hPdet hCdet hΔ hQ u

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticStepWeight
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial weights for the quadratic cascade recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavityQuadraticStepWeight_eq_normalized {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u z : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticStepWeight K P C ζ (u, z) =
      Real.exp (((ζ / 2 * ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (cavityBackwardQuadratic K C) (u + z)⟫) -
        Real.log (∫ x : EuclideanSpace ℝ (Fin d), Real.exp
          (ζ / 2 * ⟪u + x, Matrix.toEuclideanCLM (𝕜 := ℝ)
            (cavityBackwardQuadratic K C) (u + x)⟫) ∂multivariateGaussian 0 S)) / ζ) := by
  have h := cavity_gaussian_recursive_logIntegral K P C S hK hC hS ζ hζ
    hPdet hCdet hΔ hQ u
  unfold cavityQuadraticStepWeight
  congr 1
  symm
  calc
    _ = ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (cavityBackwardQuadratic K C) (u + z)⟫ / 2 -
        (1 / ζ) * Real.log (∫ x : EuclideanSpace ℝ (Fin d), Real.exp
          (ζ / 2 * ⟪u + x, Matrix.toEuclideanCLM (𝕜 := ℝ)
            (cavityBackwardQuadratic K C) (u + x)⟫) ∂multivariateGaussian 0 S) := by
      field_simp [hζ.ne']
    _ = _ := by rw [h]; ring

/-- The concrete backward polynomial weight supplies the normalized
innovation law required at every ancestor in `cavityInnovationTree_law`. -/
theorem cavity_quadratic_step_weight_innovation_law {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 S).withDensity
      (fun z => ENNReal.ofReal (cavityQuadraticStepWeight K P C ζ (u, z) ^ ζ))).map
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (u + z) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ u) =
      multivariateGaussian 0
        ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) := by
  simp_rw [cavityQuadraticStepWeight_eq_normalized K P C S hK hC hS ζ hζ
    hPdet hCdet hΔ hQ u]
  exact cavity_retained_gaussian_innovation_law K P C S hK hC hS ζ hζ.ne'
    hPdet hCdet hΔ hQ u

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian innovations for the retained finite quadratic tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityStepInnovation {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (cavityStepInnovation K P C) := by
  unfold cavityStepInnovation
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationPrefix
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic innovation change preserves shared Gaussian prefixes.
This is the deterministic part of transporting common-level spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix Classical

namespace InvariantIsing

lemma cavityCommonMarkDepth_measurable {d : ℕ} (n : ℕ) :
    Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n => cavityCommonMarkDepth n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [cavityCommonMarkDepth]
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    · have ht : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) ×
          NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) => (p.1.2.2, p.2.2.2)) := by fun_prop
      exact (ih.comp ht).add_const 1
    · exact measurable_const

lemma cavityStepInnovation_injective {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (hC : IsUnit (1 - C * K).det)
    (s : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (fun a => cavityStepInnovation K P C (s, a)) := by
  have hi : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹) := by
    apply Function.LeftInverse.injective (g := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K))
    intro x
    rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_nonsing_inv _ hC,
      map_one, one_apply_eq_self]
  intro a b hab
  apply add_left_cancel (a := s)
  apply hi
  exact (sub_left_inj).mp hab

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationCovariancePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the noncommuting innovation covariance. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_innovation_covariance_posSemidef {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (ζ : ℝ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) :
    ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose).PosSemidef := by
  have hcov : cavityStepTransition K P C * S =
      cavityResolvent (ζ • cavityBackwardQuadratic K C) S := by
    unfold cavityStepTransition cavityResolvent
    rw [hΔ]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [← cavity_rescaled_step_covariance K P C S hPdet hCdet, hcov]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (cavity_tilt_covariance_posSemidef (ζ • cavityBackwardQuadratic K C) S hS hQ).mul_mul_conjTranspose_same
      (1 - C * K)⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common depths alone are preserved by the same-root quadratic innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityRootedDepthTest {d k n : ℕ} (a : ℕ → ℝ) :
    Measurable (cavityRootedDepthTest (d := d) (k := k) (n := n) a) := by
  have hc : Measurable (fun σ : ℕ → CavitySpinState d k n =>
      cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) :=
    (cavityCommonMarkDepth_measurable n).comp
      (show Measurable (fun σ : ℕ → CavitySpinState d k n =>
        ((σ 0).1.2.1, (σ 1).1.2.1)) from by fun_prop)
  exact (measurable_of_countable a).comp hc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedDepthMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded common-depth observable disintegrated over root and forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_cavityRootedDepthTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) :
    Measurable (cavityRootedDepthTestMean n K R L C π a) := by
  let κ := probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
    (cavityRootedFullGibbs n K R L C π).measurable
  exact (((measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a).comp
    measurable_snd).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityRootedDepthTest_abs_le {d k n : ℕ} (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) (σ : ℕ → CavitySpinState d k n) :
    |cavityRootedDepthTest a σ| ≤ B := by
  simpa only [cavityRootedDepthTest, abs_mul, abs_spinValue, mul_one, one_mul] using
    ha (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

lemma cavityRootedDepthTestMean_abs_le {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) {B : ℝ} (ha : ∀ i, |a i| ≤ B)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    |cavityRootedDepthTestMean n K R L C π a ω| ≤ B :=
  abs_integral_le_const_of_bound (measurable_cavityRootedDepthTest a)
    (cavityRootedDepthTest_abs_le a ha)

theorem cavity_rooted_depth_test_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [IsProbabilityMeasure P] (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)) =
      ∫ ω, cavityRootedDepthTestMean n K R L C π a ω ∂P := by
  have hi := integrable_of_measurable_abs_le
    (μ := (probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)
    (measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a)
    (cavityRootedDepthTest_abs_le a ha)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  simpa only [Kernel.const_apply, probabilityReplicaKernel, Kernel.coe_mk,
    cavityRootedDepthTestMean] using
    Kernel.integral_comp hi

theorem cavity_rooted_depth_test_product_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)) [IsProbabilityMeasure Q]
    (a : ℕ → ℝ) {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P.prod Q)) =
      ∫ s, ∫ V, cavityRootedDepthTestMean n K R L C π a (s, V) ∂Q ∂P := by
  rw [cavity_rooted_depth_test_disintegration n K R L C π (P.prod Q) a ha]
  exact integral_prod _ (integrable_of_measurable_abs_le
    (measurable_cavityRootedDepthTestMean n K R L C π a)
    (cavityRootedDepthTestMean_abs_le n K R L C π a ha))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationAtomless
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomlessness passes through the actual weighted affine Gaussian innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder

namespace InvariantIsing

lemma cavity_nullSingleton_map {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [NullSingletonClass μ]
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : Measurable f) (hi : Function.Injective f) : NullSingletonClass (μ.map f) := by
  constructor
  intro x
  rw [Measure.map_apply hf (measurableSet_singleton x)]
  by_cases h : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := h
    have hp : f ⁻¹' {f y} = {y} := by
      ext z
      exact hi.eq_iff
    rw [hp, measure_singleton]
  · have hp : f ⁻¹' {x} = ∅ := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [hp, measure_empty]

lemma cavity_quadratic_innovation_nullSingleton {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C) (CFC.sqrt S)).PosDef)
    [NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)] :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose)) := by
  let μ := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).withDensity
    (fun a => ENNReal.ofReal (cavityQuadraticStepWeight K P C ζ (0, a) ^ ζ))
  let f := fun a : EuclideanSpace ℝ (Fin d) => cavityStepInnovation K P C (0, a)
  have hm : Measurable f :=
    (measurable_cavityStepInnovation K P C).comp (measurable_const.prodMk measurable_id)
  have hi : Function.Injective f := cavityStepInnovation_injective K P C hCdet 0
  have ha : NullSingletonClass (μ.map f) := cavity_nullSingleton_map μ f hm hi
  have he : μ.map f = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) :=
    cavity_quadratic_step_weight_innovation_law K P C S hK hC hS ζ hζ hPdet hCdet hΔ hQ 0
  exact he ▸ ha

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDepthTestEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic cavity tilt preserves the common-level distribution. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

theorem cavity_full_depth_test_evaluation_oai (hpub : PanchenkoTalagrandFieldPairInput)
    {d k : ℕ} (hk : 0 < k) (h : FieldStep)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef)
    (hb : ∀ i, 0 < chainExponent h.cut i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = chainExponent h.cut i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (chainExponent h.cut i • cavityBackwardQuadratic K (H (i + 1)))
        (CFC.sqrt (S i))).PosDef)
    (hR : (H h.depth).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H h.depth))).PosDef)
    (hAtom : ∀ i < h.depth,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)))
    (v : ℝ≥0)
    (hcov : ∀ i < h.depth,
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1)
    (hres : L.transpose * cavityResolvent K (H h.depth) * L = (v : ℝ) • 1)
    (ψ : ℕ → ℝ)
    {B : ℝ} (hψ : ∀ i, |ψ i| ≤ B) :
    (∫ σ, cavityRootedDepthTest ψ σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (uniformSpinPrior k))
        (cavityRootedFullGibbs h.depth K (H h.depth) L (c • 1) (uniformSpinPrior k)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth (chainExponent h.cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure := by
  let b := chainExponent h.cut
  let S' := fun i => (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose
  let S₀' := (1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose
  let R := cavityResolvent K (H h.depth)
  have hbC := chainExponent_admissible h.ordered_cut h.first h.last
  have hS' (i : ℕ) : (S' i).PosSemidef :=
    cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
      (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  have hR' : R.PosSemidef := cavity_tilt_covariance_posSemidef K (H h.depth) hR hQR
  have hAtom' (i : ℕ) (hi : i < h.depth) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S' i)) := by
    let := hAtom i hi
    exact cavity_quadratic_innovation_nullSingleton K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  rw [cavity_rooted_depth_test_transport h.depth K H S b S₀ hS₀ L (c • 1)
    hbC hK hH hS hb hdet hΔ hQ hR hQR (uniformSpinPrior k)]
  rw [cavity_rooted_depth_test_product_disintegration h.depth 0 R L (c • 1)
    (uniformSpinPrior k) (multivariateGaussian 0 S₀')
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) h.depth b (cavityGaussianMarks S') : Measure _)
    ψ hψ]
  trans (∫ _s : EuclideanSpace ℝ (Fin d), (∫ t, ψ (fieldLevelIndex h t).val ∂pathMeasure)
    ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀')
  · apply integral_congr_ae
    exact ae_of_all _ (fun s => cavity_linear_rooted_depth_evaluation hpub hk h S' hS' hAtom' R hR'
      L v hcov hres c s ψ hψ)
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_full_depth_test_evaluation_oai := @OAI.InvariantIsing.cavity_full_depth_test_evaluation_oai
