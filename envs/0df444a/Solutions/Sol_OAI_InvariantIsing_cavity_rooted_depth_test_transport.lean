-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_rooted_depth_test_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:06.278211+00:00
-- url     : https://prove2.me/submissions/44418ca4-797a-49c3-b5ae-4a7ae1b9c7ee

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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_quadratic_regular_ae
import Theorems.Thm_OAI_InvariantIsing_cavity_quadratic_root_tree_law
import Theorems.Thm_OAI_InvariantIsing_cavity_residual_innovation_leaf_law
import Theorems.Thm_OAI_InvariantIsing_cavity_residual_partition_pos_finite
import Theorems.Thm_OAI_InvariantIsing_cavity_rooted_quadratic_gaussian

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

variable {E : Type*} [MeasurableSpace E]

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)



omit [Nonempty E] in
lemma measurable_sigmaPart_param (μ : Measure E) [SigmaFinite μ]
    {A : Type*} [MeasurableSpace A] {N : A → Measure E} (hN : Measurable N)
    {F : A × E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂sigmaPart μ (N a)) := by
  simp only [sigmaPart, lintegral_sum_measure]
  apply Measurable.tsum
  intro n
  exact measurable_finitePart_param
    ((measurable_measureRestrict (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)).comp hN) hF

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace
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

lemma measurable_map_sigmaPart_param {E F P : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace P] (μ : Measure E) [SigmaFinite μ]
    {N : P → Measure E} (hN : Measurable N) {G : P × E → F} (hG : Measurable G) :
    Measurable (fun p => (sigmaPart μ (N p)).map (fun x => G (p,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun p : P × E => s.indicator (1 : F → ℝ≥0∞) (G p)) :=
    (measurable_const.indicator hs).comp hG
  convert measurable_sigmaPart_param μ hN hf using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [Measure.map_apply (f := fun x => G (p,x))
    (hG.comp (measurable_const.prodMk measurable_id)) hs]
  exact (lintegral_indicator_one (hs.preimage
    (hG.comp (measurable_const.prodMk measurable_id)))).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseTreeKeep
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeKeep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeKeep n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeKeep
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1, (p.2.2.1,
          noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)))
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
          (ℝ × (A × NoiseTree A n)) => p.2.2.1)).prodMk
        ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma measurableSet_noiseGibbsRegular (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    MeasurableSet {p : S × NoiseTree A n | NoiseGibbsRegular n b μ c u p.1 p.2} := by
  induction n generalizing b μ c u with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot : Measurable (fun p : S × NoiseTree A (n+1) => noiseTreeTotal A (n+1) p.2) :=
      (measurable_noiseTreeTotal A (n+1)).comp measurable_snd
    have hkeep : Measurable (fun p : S × NoiseTree A (n+1) =>
        noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u p.1 p.2)) :=
      (measurable_noiseTreeTotal A (n+1)).comp (measurable_noiseTreeKeep (n+1) b μ hc hu)
    have hgood : MeasurableSet {p : S × NoiseTree A (n+1) | Marked.PoissonGood I p.2} :=
      by
        simp only [Marked.PoissonGood, ofPred_forall]
        exact MeasurableSet.iInter (fun j => measurableSet_lt
          ((Measure.measurable_coe (MeasurableSet.disjointed (measurableSet_spanningSets I) j)).comp measurable_snd)
          (measurable_const (a := (∞ : ℝ≥0∞))))
    let B := {p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) |
      ¬ NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2}
    have hB : MeasurableSet B :=
      ((ih _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))).compl
    have hm : Measurable (fun p : S × NoiseTree A (n+1) =>
        ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) :=
      measurable_sigmaPart_param I measurable_snd (measurable_const.indicator hB)
    have he : {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} =
        {p | (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) = 0} := by
      ext p
      rw [mem_ofPred_eq, mem_ofPred_eq, ae_iff]
      change (sigmaPart I p.2) {x | (p,x) ∈ B} = 0 ↔ _
      have hh := lintegral_indicator_one (μ := sigmaPart I p.2)
        (show MeasurableSet {x : ℝ × (A × NoiseTree A n) | (p,x) ∈ B} from
          hB.preimage (measurable_const.prodMk measurable_id))
      simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using Iff.of_eq (congrArg (· = 0) hh).symm
    have htail : MeasurableSet {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} := by
      rw [he]
      exact measurableSet_eq_fun hm measurable_const
    exact ((measurableSet_lt measurable_const htot).inter (measurableSet_lt htot measurable_const)).inter
      (((measurableSet_lt measurable_const hkeep).inter (measurableSet_lt hkeep measurable_const)).inter
        (hgood.inter htail))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron



lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma integral_tilted_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) :
    (∫ x, F x ∂ν.tilted H) = (∫ x, Real.exp (H x)*F x ∂ν)/(∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

lemma measurable_random_tilted_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H F : Ω × X → ℝ} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun ω => ∫ x, F (ω,x) ∂(ν ω).tilted (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  simp_rw [integral_tilted_ratio]
  exact ((hH.exp.mul hF).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((hH.exp).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
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
namespace IsingPerceptron

lemma kernel_comap_comp_measure {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] (P : Measure Ω) (K : Kernel Ω' X) {T : Ω → Ω'} (hT : Measurable T) :
    K.comap T hT ∘ₘ P = K ∘ₘ P.map T := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),Measure.bind_apply hs K.aemeasurable,
    lintegral_map (K.measurable_coe hs) hT]
  rfl

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_bilinear_abs_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin d → ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ b) :
    |∑ i, ∑ j, x i * A i j * y j| ≤ cavityMatrixMass A * (a * b) := by
  calc
    _ ≤ ∑ i, |∑ j, x i * A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (a * b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |A i j| * (|x i| * |y j|) := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) ha)
          (abs_nonneg _)
    _ = _ := by simp only [cavityMatrixMass, Finset.sum_mul]

lemma cavity_spin_quadratic_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    |cavityQuadratic A (fun j => spinValue (ε j))| ≤ cavityMatrixMass A := by
  have h := cavity_bilinear_abs_bound A (fun j => spinValue (ε j)) (fun j => spinValue (ε j))
    zero_le_one zero_le_one (fun i => (abs_spinValue (ε i)).le) (fun i => (abs_spinValue (ε i)).le)
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := cavityMatrixMass_nonneg A
  simp only [mul_one] at h
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianEnvelope
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial-exponential moments for the finite Gaussian marks
after the quadratic tilt. Only the norm of the covariance factor matters. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_standardGaussian_exp_norm_integrable (d : ℕ) (c : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (c * ‖z‖)) (stdGaussian _) := by
  obtain ⟨a, ha, hi⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian (EuclideanSpace ℝ (Fin d)))
  let b := c^2 / (4 * a)
  have hb : 4 * a * b = c^2 := mul_div_cancel₀ _ (by positivity)
  apply (hi.const_mul (Real.exp b)).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs := sq_nonneg (2 * a * ‖z‖ - c)
    nlinarith

lemma cavity_polynomial_exp_bound (p : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    r^p * Real.exp (c * r) ≤ Real.exp ((p + c) * r) := by
  have he : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hp := pow_le_pow_left₀ hr he p
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (c * r)).le
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hm
  simpa only [add_mul] using hm

theorem cavity_gaussian_linear_polynomial_exp_bound {d q : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin q))
    {M c : ℝ} (_hM : 0 ≤ M) (hL : ‖L‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) ∧
    (∫ z : EuclideanSpace ℝ (Fin d), ‖L z‖^p * Real.exp (c * ‖L z‖) ∂stdGaussian _) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), Real.exp (((p : ℝ) + c) * M * ‖z‖) ∂stdGaussian _ := by
  have hi := cavity_standardGaussian_exp_norm_integrable d (((p : ℝ) + c) * M)
  have hb z : ‖L z‖^p * Real.exp (c * ‖L z‖) ≤ Real.exp (((p : ℝ) + c) * M * ‖z‖) := by
    have hn : ‖L z‖ ≤ M * ‖z‖ := (L.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
    apply (cavity_polynomial_exp_bound p c ‖L z‖ (norm_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (add_nonneg (Nat.cast_nonneg p) hc)]
  have hif : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) := by
    apply hi.mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb z
  exact ⟨hif, integral_mono hif hi hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearTiltMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moments after the remaining linear tilt can be bounded using only
one-replica Gaussian moments, by Jensen and the elementary product bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_linear_tilt_moment_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V f : X → ℝ)
    (hV : Integrable V ν) (he : Integrable (fun x => Real.exp (V x)) ν)
    (heNeg : Integrable (fun x => Real.exp (-V x)) ν) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : Integrable (fun x => f x * Real.exp (V x)) ν)
    (hfe2 : Integrable (fun x => (f x * Real.exp (V x))^2) ν)
    (heNeg2 : Integrable (fun x => Real.exp (-V x)^2) ν) :
    (∫ x, f x ∂ν.tilted V) ≤
      ((∫ x, (f x * Real.exp (V x))^2 ∂ν) + (∫ x, Real.exp (-V x)^2 ∂ν)) / 2 := by
  have hJ := partition_inv_pow_le (ν := ν) (H := V) 1 hV he (by
    simpa only [Nat.cast_one, neg_mul, one_mul] using heNeg)
  simp only [pow_one, Nat.cast_one, neg_mul, one_mul] at hJ
  have hA0 : 0 ≤ ∫ x, f x * Real.exp (V x) ∂ν := integral_nonneg
    (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
  have hA := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)) hfe hfe2
  have hB := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => (Real.exp_pos (-V x)).le)) heNeg heNeg2
  have hbound := mul_le_mul_of_nonneg_left hJ hA0
  rw [integral_tilted_eq_div]
  have hswap : (∫ x, Real.exp (V x) * f x ∂ν) = ∫ x, f x * Real.exp (V x) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [hswap, div_eq_mul_inv]
  nlinarith [sq_nonneg ((∫ x, f x * Real.exp (V x) ∂ν) - ∫ x, Real.exp (-V x) ∂ν)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearEnvelope
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform moments of the remaining linear cavity tilt. The estimate uses
only the one-replica exponential radial moment after the quadratic tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma cavity_linear_logFactor_growth {d n : ℕ}
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor 0 L C y ε| ≤
      (cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖) := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) y = 0 := by
    simp [cavityQuadratic]
  simp only [mul_one] at hL
  simp only [cavityLogFactor, hz, zero_add]
  apply (abs_add_le _ _).trans
  nlinarith [cavityMatrixMass_nonneg L, cavityMatrixMass_nonneg C, norm_nonneg y,
    mul_nonneg (cavityMatrixMass_nonneg C) (norm_nonneg y)]

lemma cavity_linear_envelope_bounds (p : ℕ) {c r v : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hv : |v| ≤ c * (1 + r)) :
    |v| ≤ c * cavityLinearMomentEnvelope p c r ∧
    Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r ∧
    r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hve := abs_le.mp hv
  have hexp : Real.exp r ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin : |v| ≤ c * cavityLinearMomentEnvelope p c r :=
    hv.trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using (Real.add_one_le_exp r).trans hexp) hc)
  have hev : Real.exp v ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hneg : Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : r^p * Real.exp v ≤ Real.exp ((p : ℝ) * r + v) := by
    have h := cavity_polynomial_exp_bound p 0 r hr
    simp only [zero_mul, Real.exp_zero, mul_one, add_zero] at h
    calc
      _ ≤ Real.exp ((p : ℝ) * r) * Real.exp v :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hprod1 : r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hprod2 : (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    apply (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr p) (Real.exp_pos _).le) hprod 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hneg2 : Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact ⟨hlin, hev, hneg, hprod1, hprod2, hneg2⟩

theorem cavity_linear_tilt_radial_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V R : X → ℝ)
    (hV : Measurable V) (hR : Measurable R) (p : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hR0 : ∀ x, 0 ≤ R x) (hv : ∀ x, |V x| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) ν) :
    Integrable (fun x => Real.exp (V x)) ν ∧
    Integrable (fun x => R x ^ p) (ν.tilted V) ∧
    (∫ x, R x ^ p ∂ν.tilted V) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂ν := by
  have hb x := cavity_linear_envelope_bounds p hc (hR0 x) (hv x)
  have hiV : Integrable V ν := (hi.const_mul c).mono' hV.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hb x).1)
  have hie : Integrable (fun x => Real.exp (V x)) ν := hi.mono' hV.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.1)
  have hin : Integrable (fun x => Real.exp (-V x)) ν := hi.mono' hV.neg.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.2.1)
  have hif : Integrable (fun x => R x^p * Real.exp (V x)) ν :=
    hi.mono' ((hR.pow_const p).mul hV.exp).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hR0 x) p) (Real.exp_pos _).le)]
        exact (hb x).2.2.2.1)
  have hif2 : Integrable (fun x => (R x^p * Real.exp (V x))^2) ν :=
    hi.mono' (((hR.pow_const p).mul hV.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.1)
  have hin2 : Integrable (fun x => Real.exp (-V x)^2) ν :=
    hi.mono' ((hV.neg.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.2)
  have hit : Integrable (fun x => R x^p) (ν.tilted V) := by
    rw [integrable_tilted_iff hie]
    simpa only [smul_eq_mul, mul_comm] using hif
  refine ⟨hie, hit, (cavity_linear_tilt_moment_bound ν V (fun x => R x^p) hiV hie hin
    (fun x => pow_nonneg (hR0 x) p) hif hif2 hin2).trans ?_⟩
  have ha := integral_mono hif2 hi (fun x => (hb x).2.2.2.2.1)
  have hn := integral_mono hin2 hi (fun x => (hb x).2.2.2.2.2)
  linarith

theorem cavity_linear_tilt_mean_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (R : X → ℝ) (hV : Measurable V) (hR : Measurable R)
    (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (hR0 : ∀ x, 0 ≤ R x)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) (κ ∘ₘ P)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => R x^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂(κ ∘ₘ P) := by
  have hia := Measure.ae_integrable_of_integrable_comp hi
  have hpoint := hia.mono fun ω hω => cavity_linear_tilt_radial_moment (κ ω)
    (fun x => V (ω, x)) R (hV.comp measurable_prodMk_left) hR p hc hR0 (hv ω) hω
  have hE : Integrable (fun ω => ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω) P := by
    have hn := Measure.integrable_integral_norm_of_integrable_comp hi
    simpa only [Real.norm_eq_abs, cavityLinearMomentEnvelope, abs_of_pos (Real.exp_pos _)] using hn
  have hm : Measurable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) :=
    measurable_random_tilted_integral κ.measurable hV
      ((hR.comp measurable_snd).pow_const p)
  have hmi : Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P :=
    hE.mono' hm.aestronglyMeasurable (hpoint.mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => pow_nonneg (hR0 x) p)]
      exact hω.2.2)
  refine ⟨hpoint.mono (fun _ h => ⟨h.1, h.2.1⟩), hmi, ?_⟩
  calc
    _ ≤ ∫ ω, ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω ∂P :=
      integral_mono_ae hmi hE (hpoint.mono fun _ h => h.2.2)
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      simpa only [Kernel.const_apply] using (Kernel.integral_comp hi).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearGaussianMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A covariance bound gives a step-independent moment bound for the
remaining cavity tilt, including singular Gaussian covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_linear_envelope {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => cavityLinearMomentEnvelope p c ‖y‖)
      (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖y‖
      ∂multivariateGaussian 0 S) ≤ cavityGaussianLinearMomentBound d p c M := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hL : ‖L‖ ≤ Real.sqrt M := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, CFC.norm_sqrt S hS.nonneg]
    exact Real.sqrt_le_sqrt hSM
  have ha : 0 ≤ (2 : ℝ) * p + 2 * c + 1 := by positivity
  have hG := cavity_gaussian_linear_polynomial_exp_bound L (Real.sqrt_nonneg M) hL ha 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hG
  have hi := hG.1.const_mul (Real.exp (2 * c))
  have he (z : EuclideanSpace ℝ (Fin d)) :
      cavityLinearMomentEnvelope p c ‖L z‖ =
        Real.exp (2 * c) * Real.exp ((2 * p + 2 * c + 1) * ‖L z‖) := Real.exp_add _ _
  have his : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      cavityLinearMomentEnvelope p c ‖y‖) (multivariateGaussian 0 S) := by
    rw [multivariateGaussian, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) (by fun_prop)]
    simpa only [zero_add, Function.comp_def, cavityLinearMomentEnvelope, Real.exp_add, L] using hi
  refine ⟨his, ?_⟩
  rw [multivariateGaussian, integral_map (by fun_prop) (by unfold cavityLinearMomentEnvelope; fun_prop)]
  simp only [zero_add]
  change (∫ z : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖L z‖ ∂stdGaussian _) ≤ _
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hG.2 (Real.exp_pos _).le

theorem cavity_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (Y : X → EuclideanSpace ℝ (Fin d))
    (hV : Measurable V) (hY : Measurable Y)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + ‖Y x‖)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => ‖Y x‖^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      cavityGaussianLinearMomentBound d p c M := by
  have hG := cavity_gaussian_linear_envelope S hS hSM hc p
  have hi : Integrable (fun x => cavityLinearMomentEnvelope p c ‖Y x‖) (κ ∘ₘ P) := by
    rw [← hLaw, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) hY.aemeasurable] at hG
    exact hG.1
  have h := cavity_linear_tilt_mean_moment P κ V (fun x => ‖Y x‖) hV hY.norm p hc
    (fun x => norm_nonneg _) hv hi
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  rw [← hLaw, integral_map hY.aemeasurable (by unfold cavityLinearMomentEnvelope; fun_prop)] at hG
  exact hG.2

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-depth retained Gaussian innovation construction.
The intensity calculation only requires the normalized conditional
fractional moment, not an ordinary exponential moment of a terminal. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma measurable_cavityInnovationTree {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityInnovationTree n b μ c g p.1 p.2) := by
  induction n generalizing b μ c g with
  | zero => exact measurable_const
  | succ n ih =>
      unfold cavityInnovationTree
      apply measurable_map_sigmaPart_param _ measurable_snd
        (G := fun p : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) (n + 1)) ×
            (ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)) =>
          (c 0 (p.1.1, p.2.2.1) * p.2.1, (g 0 (p.1.1, p.2.2.1),
            cavityInnovationTree n (fun j => b (j + 1)) (fun j => μ (j + 1))
              (fun j => c (j + 1)) (fun j => g (j + 1)) (p.1.1 + p.2.2.1) p.2.2.2)))
      apply Measurable.prodMk
      · exact ((hc 0).comp (by fun_prop)).mul (by fun_prop)
      · apply Measurable.prodMk ((hg 0).comp (by fun_prop))
        exact (ih _ _ _ _ (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
          ((measurable_fst.fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticStepWeight
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma measurable_cavityQuadraticStepWeight {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) :
    Measurable (cavityQuadraticStepWeight K P C ζ) := by
  unfold cavityQuadraticStepWeight
  fun_prop

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationLeaves
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Leaf transport for the retained quadratic innovation tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma measurable_cavityInnovationLeaf {d : ℕ} (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      cavityInnovationLeaf n c g p.1 p.2) := by
  induction n generalizing c g with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      (((hg 0).comp (by fun_prop)).prodMk
        ((ih _ _ (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
          ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)))

/-- The transformed increments telescope to the rescaled final sum. -/
theorem cavityInnovationLeaf_sum {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s v) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s v) := by
  induction n generalizing H c s with
  | zero => rfl
  | succ n ih =>
    simp only [cavityLeafSum, cavityInnovationLeaf]
    have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s +
        cavityStepInnovation K (H 0) (H 1) (s, v.2.1) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 1 * K)⁻¹ (s + v.2.1) := by
      unfold cavityStepInnovation
      abel
    rw [he]
    exact ih (fun i => H (i + 1)) (fun i => c (i + 1)) (s + v.2.1) v.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unnormalized leaf-kernel transport under the innovation map. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma cavity_replica_kernel_transport {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (P : Measure Ω) (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure X}
    (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {L : X → X} (hL : Measurable L)
    (h : ∀ᵐ ω ∂P, (ν ω).map L = κ (T ω)) :
    ((probabilityReplicaKernel ν hν) ∘ₘ P).map (fun σ i => L (σ i)) =
      (probabilityReplicaKernel κ hκ) ∘ₘ Q := by
  let K := probabilityReplicaKernel κ hκ
  have hLs : Measurable (fun σ : ℕ → X => fun i => L (σ i)) := by fun_prop
  rw [Measure.map_comp _ _ hLs]
  calc
    _ = K.comap T hT ∘ₘ P := by
      apply Measure.comp_congr
      filter_upwards [h] with ω hω
      simp only [Kernel.map_apply _ hLs, Kernel.comap_apply, probabilityReplicaKernel, K]
      change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => L (σ i)) =
        Measure.infinitePi (fun _ : ℕ => κ (T ω))
      rw [Measure.infinitePi_map_pi _ (fun _ => hL)]
      simp only [hω]
    _ = K ∘ₘ Q := by rw [kernel_comap_comp_measure, hPQ]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualInnovation
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint innovation map for a true cascade leaf and its ordinary
terminal residual. All residual randomness remains outside the cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityResidualInnovationMap {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) : Measurable (cavityResidualInnovationMap n K H b s) := by
  have hL : Measurable (cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1))) s) :=
    (measurable_cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1)))
    (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
    (fun i => measurable_cavityStepInnovation _ _ _)).comp
      (measurable_const.prodMk measurable_id)
  have hs := measurable_cavityLeafSum n s
  unfold cavityResidualInnovationMap
  exact (hL.comp measurable_fst).prodMk
    (((hs.comp measurable_fst).add measurable_snd).sub
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹).measurable.comp
        (hs.comp measurable_fst)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticOneReplica
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-replica marginal after the quadratic cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_residual_innovation_sum {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :
    cavityLeafSum n (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
        (cavityResidualInnovationMap n K H b s p).1 +
      (cavityResidualInnovationMap n K H b s p).2 = cavityLeafSum n s p.1 + p.2 := by
  dsimp only [cavityResidualInnovationMap]
  rw [cavityInnovationLeaf_sum]
  abel

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinLinearMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining linear/spin tilt preserves uniform Gaussian radial moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_independent_spin_marginal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (fun x => Y x.1) = (κ ∘ₘ P).map Y := by
  change ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (Y ∘ Prod.fst) = _
  rw [← Measure.map_map hY measurable_fst, Measure.map_comp P _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]

theorem cavity_spin_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    {M : ℝ} (hSM : ‖S‖ ≤ M) (p : ℕ) :
    let ν := κ ×ₖ Kernel.const Ω π
    let V := fun x : X × Spin k => cavityLogFactor 0 L C (Y x.1) x.2
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V x)) (ν ω) ∧
      Integrable (fun x => ‖Y x.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) M := by
  intro ν V
  have hv : Measurable V := by
    unfold V cavityLogFactor cavityQuadratic
    have hy : ∀ i, Measurable (fun x : X × Spin k => Y x.1 i) :=
      fun i => (EuclideanSpace.proj i).measurable.comp (hY.comp measurable_fst)
    have he : ∀ i, Measurable (fun x : X × Spin k => spinValue (x.2 i)) := by
      intro i
      exact (measurable_of_countable (spinValue : Bool → ℝ)).comp
        ((measurable_pi_apply i).comp measurable_snd)
    fun_prop
  exact cavity_linear_tilt_gaussian_moment P ν (fun x => V x.2) (fun x => Y x.1)
    (hv.comp measurable_snd) (hY.comp measurable_fst) S hS
    ((cavity_independent_spin_marginal P κ Y hY π).trans hLaw) hSM
    (add_nonneg (cavityMatrixMass_nonneg L) (cavityMatrixMass_nonneg C)) p
    (fun _ x => cavity_linear_logFactor_growth L C (Y x.1) x.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTilt
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullGibbs
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
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

theorem cavityInnovationLeaf_commonMarkDepth {d : ℕ} (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ∀ i s, Function.Injective (fun a => g i (s, a)))
    (s : EuclideanSpace ℝ (Fin d))
    (v w : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityCommonMarkDepth n (cavityInnovationLeaf n c g s v)
      (cavityInnovationLeaf n c g s w) = cavityCommonMarkDepth n v w := by
  classical
  induction n generalizing c g s with
  | zero => rfl
  | succ n ih =>
    by_cases h : v.2.1 = w.2.1
    · simp only [cavityInnovationLeaf, cavityCommonMarkDepth, h, ite_true, if_true]
      rw [ih _ _ (fun i => hg (i + 1))]
    · have hh : g 0 (s, v.2.1) ≠ g 0 (s, w.2.1) := (hg 0 s).ne h
      simp only [cavityInnovationLeaf, cavityCommonMarkDepth, h, hh, ite_false, if_false]

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

theorem cavityQuadraticInnovation_commonMarkDepth {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (hdet : ∀ i, IsUnit (1 - H i * K).det) (s : EuclideanSpace ℝ (Fin d))
    (v w : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityCommonMarkDepth n
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s v)
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s w) =
        cavityCommonMarkDepth n v w := by
  classical
  exact cavityInnovationLeaf_commonMarkDepth n c _
    (fun i => cavityStepInnovation_injective K (H i) (H (i + 1)) (hdet (i + 1))) s v w

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinTiltTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining finite Ising tilt commutes with the actual quadratic
innovation change of variables, including the ordinary residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityLinearResidualPotential {d k : ℕ} (n : ℕ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin d)) : Measurable (cavityLinearResidualPotential n L C s) := by
  let E := (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k
  have hs : Measurable (fun p : E =>
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d))) :=
    ((measurable_cavityLeafSum n s).comp (measurable_fst.comp measurable_fst)).add
      (measurable_snd.comp measurable_fst)
  have hy (i : Fin d) : Measurable (fun p : E =>
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp hs
  have he (i : Fin k) : Measurable (fun p : E => spinValue (p.2 i)) :=
    (measurable_of_countable (spinValue : Bool → ℝ)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have hL : Measurable (fun p : E => ∑ i, ∑ j,
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) i * L i j *
        spinValue (p.2 j)) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (L i j)).mul (he j)))
  have hC : Measurable (fun p : E => cavityQuadratic C (fun i => spinValue (p.2 i))) :=
    (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((he i).mul_const (C i j)).mul (he j)))).const_mul (1 / 2)
  change Measurable (fun p : E => cavityLogFactor 0 L C
    (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
  convert hL.add hC using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp [cavityLogFactor, cavityQuadratic]

theorem cavity_spin_tilt_innovation_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    (((cavityQuadraticResidualGibbs n K (H n) s V).prod π).tilted
      (cavityLinearResidualPotential n L C s)).map
        (Prod.map (cavityResidualInnovationMap n K H b s) id) =
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
            (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π).tilted
        (cavityLinearResidualPotential n L C
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)) := by
  let T := Prod.map (cavityResidualInnovationMap n K H b s) (id : Spin k → Spin k)
  let s' := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b s).prodMap measurable_id
  have hfun : cavityLinearResidualPotential n L C s =
      cavityLinearResidualPotential n L C s' ∘ T := by
    funext p
    dsimp only [cavityLinearResidualPotential, Function.comp_def, T, Prod.map, id_eq, s']
    rw [cavity_residual_innovation_sum]
  rw [hfun, cavity_tilt_map _ T hT _ (measurable_cavityLinearResidualPotential n L C s')]
  rw [show T = Prod.map (cavityResidualInnovationMap n K H b s) id from rfl,
    ← Measure.map_prod_map _ _ (measurable_cavityResidualInnovationMap n K H b s) measurable_id,
    Measure.map_id]
  have he := cavity_residual_innovation_leaf_law n K H S b hK hR hdet hQ s V hZ hV
  change (cavityQuadraticResidualGibbs n K (H n) s V).map
    (cavityResidualInnovationMap n K H b s) = _ at he
  rw [he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinFullLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-factor spin law before and after the quadratic innovation
change of variables. The ordinary residual is part of each probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma cavityQuadraticResidualGibbs_eq_tilted {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    cavityQuadraticResidualGibbs n K R s V =
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
        (multivariateGaussian 0 R)).tilted
          (fun p => ⟪cavityLeafSum n s p.1 + p.2,
            Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
  have hm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  exact normalizeMass_exp _ _ hm (cavity_residual_quadratic_integrable n K R s V hZ)

theorem cavityResidualSpinFullLaw_eq_successive {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) (π : Measure (Spin k))
    [IsProbabilityMeasure π] (hZ : cavityResidualPartition n K R s V < ∞) :
    cavityResidualSpinFullLaw n K R L C s V π =
      ((cavityQuadraticResidualGibbs n K R s V).prod π).tilted
        (cavityLinearResidualPotential n L C s) := by
  have hm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  rw [cavityQuadraticResidualGibbs_eq_tilted n K R s V hZ,
    cavity_tilt_prod_left _ π _ hm,
    tilted_tilted ((cavity_residual_quadratic_integrable n K R s V hZ).comp_fst π)]
  unfold cavityResidualSpinFullLaw
  congr 1
  funext p
  exact (cavity_rooted_exponent_split n K L C ((s, p.1), p.2)).symm

theorem cavity_full_spin_innovation_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    (cavityResidualSpinFullLaw n K (H n) L C s V π).map
        (Prod.map (cavityResidualInnovationMap n K H b s) id) =
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
            (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π).tilted
        (cavityLinearResidualPotential n L C
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)) := by
  rw [cavityResidualSpinFullLaw_eq_successive n K (H n) L C s V π hZ]
  exact cavity_spin_tilt_innovation_transport n K H S b L C hK hR hdet hQ s V hZ hV π

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
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

lemma cavityRootedFullGibbs_eq_residual_map {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R (s, V)).prod π)) :
    cavityRootedFullGibbs n K R L C π (s, V) =
      (cavityResidualSpinFullLaw n K R L C s V π).map (cavityAttachSpinRoot n s) := by
  rw [cavityRootedFullGibbs_eq_tilted n K R L C π (s, V) he]
  let μ := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).prod π
  let A := cavityAttachSpinRoot (k := k) n s
  let F := fun z : CavitySpinState d k n => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  have hp : (cavityRootedPriorKernel n R (s, V)).prod π = μ.map A := by
    rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
      Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
    have hA : A = Prod.map (Prod.mk s) (id : Spin k → Spin k) := by
      funext p
      rfl
    rw [hA]
    simpa only [Measure.map_id, μ] using Measure.map_prod_map
      ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
      (show Measurable (Prod.mk s :
        NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) ×
            (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) from
              measurable_const.prodMk measurable_id) measurable_id
  rw [hp]
  change (μ.map A).tilted F = (μ.tilted (F ∘ A)).map A
  exact (cavity_tilt_map μ A (measurable_cavityAttachSpinRoot n s)
    F (measurable_cavityRootedLogFactor n K L C)).symm

lemma measurable_cavityRootedSpinInnovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) : Measurable (cavityRootedSpinInnovation (k := k) n K H b) := by
  unfold cavityRootedSpinInnovation cavityResidualInnovationMap
  have hm := measurable_cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1)))
    (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
    (fun i => measurable_cavityStepInnovation _ _ _)
  have hs := measurable_cavityLeafSum_joint (d := d) n
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the remaining spin exponential integrability through the
quadratic innovation law. No integrability of the transformed tilt is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal RealInnerProductSpace

namespace InvariantIsing

lemma cavityRootedPrior_spin_eq_map {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    (cavityRootedPriorKernel n R (s, V)).prod π =
      ((((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)).prod π).map
        (cavityAttachSpinRoot n s)) := by
  rw [cavityRootedPriorKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  have hA : cavityAttachSpinRoot (k := k) n s = Prod.map (Prod.mk s) id := by
    funext p
    rfl
  rw [hA]
  simpa only [Measure.map_id] using Measure.map_prod_map
    ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod (multivariateGaussian 0 R)) π
    (show Measurable (Prod.mk s :
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d) ×
          (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) from
            measurable_const.prodMk measurable_id) measurable_id

theorem cavity_spin_innovation_exp_integrable {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (H n) (s, V)).prod π)) :
    let s' := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s
    let V' := cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V
    Integrable (fun z => Real.exp (cavityLogFactor 0 L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (cavityResolvent K (H n)) (s', V')).prod π) := by
  intro s' V'
  let E := (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k
  let μ := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 (H n))).prod π
  let Q := fun p : E => ⟪cavityLeafSum n s p.1.1 + p.1.2,
    Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1.1 + p.1.2)⟫ / 2
  let F := cavityLinearResidualPotential n L C s
  let T := Prod.map (cavityResidualInnovationMap n K H b s) (id : Spin k → Spin k)
  let η := ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V').prod
    (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b s).prodMap measurable_id
  have hQm : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => ⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2) := by
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have hiQ : Integrable (fun p => Real.exp (Q p)) μ :=
    (cavity_residual_quadratic_integrable n K (H n) s V hZ).comp_fst π
  have hraw : Integrable (fun p : E => Real.exp (Q p + F p)) μ := by
    rw [cavityRootedPrior_spin_eq_map n (H n) π s V] at he
    have hi := (integrable_map_measure
      ((measurable_cavityRootedLogFactor n K L C).exp.aestronglyMeasurable)
      (measurable_cavityAttachSpinRoot n s).aemeasurable).mp he
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact congrArg Real.exp (cavity_rooted_exponent_split n K L C ((s, p.1), p.2))
  have hq : (cavityQuadraticResidualGibbs n K (H n) s V).prod π = μ.tilted Q := by
    rw [cavityQuadraticResidualGibbs_eq_tilted n K (H n) s V hZ,
      cavity_tilt_prod_left _ π _ hQm]
  have hlin : Integrable (fun p => Real.exp (F p))
      ((cavityQuadraticResidualGibbs n K (H n) s V).prod π) := by
    rw [hq, integrable_tilted_iff hiQ]
    simpa only [smul_eq_mul, ← Real.exp_add] using hraw
  have hmap : ((cavityQuadraticResidualGibbs n K (H n) s V).prod π).map T = η := by
    rw [show T = Prod.map (cavityResidualInnovationMap n K H b s) id from rfl,
      ← Measure.map_prod_map _ _ (measurable_cavityResidualInnovationMap n K H b s) measurable_id,
      Measure.map_id]
    have hlaw := cavity_residual_innovation_leaf_law n K H S b hK hR hdet hQ s V hZ hV
    change (cavityQuadraticResidualGibbs n K (H n) s V).map
      (cavityResidualInnovationMap n K H b s) = _ at hlaw
    rw [hlaw]
  have hF : Measurable (cavityLinearResidualPotential n L C s') :=
    measurable_cavityLinearResidualPotential n L C s'
  have hpull : (fun p => Real.exp (cavityLinearResidualPotential n L C s' (T p))) =
      fun p => Real.exp (F p) := by
    funext p
    dsimp only [F, T, Prod.map, id_eq, cavityLinearResidualPotential, s']
    rw [cavity_residual_innovation_sum]
  have hi : Integrable (fun p => Real.exp (cavityLinearResidualPotential n L C s' p)) η := by
    rw [← hmap]
    apply (integrable_map_measure hF.exp.aestronglyMeasurable hT.aemeasurable).mpr
    change Integrable (fun p => Real.exp (cavityLinearResidualPotential n L C s' (T p))) _
    rwa [hpull]
  rw [cavityRootedPrior_spin_eq_map n (cavityResolvent K (H n)) π s' V']
  exact (integrable_map_measure
    ((measurable_cavityRootedLogFactor n 0 L C).exp.aestronglyMeasurable)
    (measurable_cavityAttachSpinRoot n s').aemeasurable).mpr hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinChange
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full spin change of variables with the common Gaussian root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavitySpinDisorderInnovation {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) : Measurable (cavitySpinDisorderInnovation n K H S b) := by
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹).measurable.comp measurable_fst).prodMk
    (measurable_cavityInnovationTree n b (cavityGaussianMarks S) _ _
      (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
      (fun i => measurable_cavityStepInnovation _ _ _))

theorem cavity_rooted_full_spin_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) ω.1 ω.2 < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) ω.1 ω.2)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n (H n) ω).prod π)) :
    (cavityRootedFullGibbs n K (H n) L C π ω).map (cavityRootedSpinInnovation n K H b) =
      cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π
        (cavitySpinDisorderInnovation n K H S b ω) := by
  have he' := cavity_spin_innovation_exp_integrable n K H S b L C hK hR hdet hQ
    ω.1 ω.2 hZ hV π he
  let ω' := cavitySpinDisorderInnovation n K H S b ω
  let T := Prod.map (cavityResidualInnovationMap n K H b ω.1) (id : Spin k → Spin k)
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b ω.1).prodMap measurable_id
  have hcomp : cavityRootedSpinInnovation (k := k) n K H b ∘ cavityAttachSpinRoot n ω.1 =
      cavityAttachSpinRoot n ω'.1 ∘ T := by
    funext p
    rfl
  rw [cavityRootedFullGibbs_eq_residual_map n K (H n) L C π ω.1 ω.2 he,
    Measure.map_map (measurable_cavityRootedSpinInnovation n K H b)
      (measurable_cavityAttachSpinRoot n ω.1), hcomp,
    ← Measure.map_map (measurable_cavityAttachSpinRoot n ω'.1) hT]
  have htr := cavity_full_spin_innovation_transport n K H S b L C hK hR hdet hQ ω.1 ω.2 hZ hV π
  change (cavityResidualSpinFullLaw n K (H n) L C ω.1 ω.2 π).map T =
    cavityResidualSpinFullLaw n 0 (cavityResolvent K (H n)) L C ω'.1 ω'.2 π at htr
  rw [htr]
  exact (cavityRootedFullGibbs_eq_residual_map n 0 (cavityResolvent K (H n)) L C π ω'.1 ω'.2 he').symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedReplicaTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many full cavity replicas under the rooted innovation change. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal BigOperators

namespace InvariantIsing

lemma cavity_rooted_full_integrability {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ ∧
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n (H n) ω).prod π) := by
  intro P
  let J₀ := (1 - H 0 * K)⁻¹
  have hZ : ∀ᵐ ω ∂P, cavityResidualPartition n K (H n) ω.1 ω.2 < ∞ := by
    have hm := measurable_cavityResidualPartition n K H b
      (Matrix.isHermitian_iff_isSymm.mpr hK) hR hQR
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hm measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      (cavity_residual_partition_pos_finite n K H S b hbCascade hK hH hS hb hdet hΔ hQ
        hR hQR s).mono (fun _ h => h.2))
  let T := J₀ * S₀ * J₀.transpose +
    ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
      cavityResolvent K (H n))
  have hT : T.PosSemidef := by
    have hroot : (J₀ * S₀ * J₀.transpose).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hS₀.mul_mul_conjTranspose_same J₀
    exact hroot.add ((Matrix.posSemidef_sum Finset.univ (fun (i : Fin n) _ =>
      cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
        (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i))).add
          (cavity_tilt_covariance_posSemidef K (H n) hR hQR))
  have hLaw : (cavityRootedResidualKernel n K (H n) ∘ₘ P).map (cavityRootedField n) =
      multivariateGaussian 0 T :=
    cavity_rooted_quadratic_gaussian n K H S b S₀ hS₀ hbCascade hK hH hS hb hdet hΔ hQ hR hQR
  have hlin := cavity_spin_linear_tilt_gaussian_moment P (cavityRootedResidualKernel n K (H n))
    (cavityRootedField n) (measurable_cavityRootedField n) π T hT hLaw L C (le_refl ‖T‖) 0
  have hfull : ∀ᵐ ω ∂P,
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n (H n) ω).prod π) := by
    filter_upwards [hZ, hlin.1] with ω hωZ hωlin
    apply cavity_rooted_full_exp_integrable n K (H n) L C π ω hωZ
    simpa only [Kernel.prod_apply, Kernel.const_apply] using hωlin.1
  filter_upwards [hZ, hfull] with ω hωZ hωfull
  exact ⟨hωZ, hωfull⟩

theorem cavity_rooted_full_replica_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    ((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
      (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P).map
        (fun σ i => cavityRootedSpinInnovation n K H b (σ i)) =
      (probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
        (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P' := by
  intro P J₀ P'
  have hPQ : P.map (cavitySpinDisorderInnovation n K H S b) = P' :=
    cavity_quadratic_root_tree_law n K H S b S₀ hS₀ hK hH hS hb hdet hΔ hQ
  have hdata := cavity_rooted_full_integrability n K H S b S₀ hS₀ L C hbCascade
    hK hH hS hb hdet hΔ hQ hR hQR π
  apply cavity_replica_kernel_transport P P'
    (cavityRootedFullGibbs n K (H n) L C π).measurable
    (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable
    (measurable_cavitySpinDisorderInnovation n K H S b) hPQ
    (measurable_cavityRootedSpinInnovation n K H b)
  have hc := fun i => measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  have hu : ∀ _i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hreg : ∀ᵐ ω ∂P, NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) ω.1 ω.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_noiseGibbsRegular n b (cavityGaussianMarks S) hc hu)).mpr
    exact Filter.Eventually.of_forall (fun s =>
      cavity_quadratic_regular_ae n K H S b hbCascade hK hH hS hb hdet hΔ hQ s)
  filter_upwards [hdata, hreg] with ω hωdata hωreg
  exact cavity_rooted_full_spin_transport n K H S b L C hK hR (hdet n) hQR
    ω hωdata.1 hωreg π hωdata.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTestTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-depth spin observable survives the full rooted quadratic
innovation change, including the disorder and all replica normalizations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityRootedFullGibbs_root_ae {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    ∀ᵐ z ∂cavityRootedFullGibbs n K R L C π ω, z.1.1 = ω.1 := by
  rw [cavityRootedFullGibbs_eq_residual_map n K R L C π ω.1 ω.2 he]
  apply (ae_map_iff (measurable_cavityAttachSpinRoot n ω.1).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  exact ae_of_all _ fun _ => rfl

lemma cavity_rooted_replicas_same_root {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    (hI : ∀ᵐ ω ∂P, Integrable
      (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    ∀ᵐ σ ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P),
        (σ 0).1.1 = (σ 1).1.1 := by
  apply Measure.ae_comp_of_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  filter_upwards [hI] with ω hω
  have hr := cavityRootedFullGibbs_root_ae n K R L C π ω hω
  have h0 := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω) 0).quasiMeasurePreserving.ae hr
  have h1 := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω) 1).quasiMeasurePreserving.ae hr
  filter_upwards [h0, h1] with σ hσ0 hσ1
  exact hσ0.trans hσ1.symm

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

lemma cavityRootedDepthTest_innovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hdet : ∀ i, IsUnit (1 - H i * K).det) (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n)
    (hroot : (σ 0).1.1 = (σ 1).1.1) :
    cavityRootedDepthTest a (fun i => cavityRootedSpinInnovation n K H b (σ i)) =
      cavityRootedDepthTest a σ := by
  unfold cavityRootedDepthTest cavityRootedSpinInnovation cavityResidualInnovationMap
  dsimp only
  rw [← hroot, cavityQuadraticInnovation_commonMarkDepth n K H _ hdet]

theorem cavity_rooted_depth_test_transport_oai {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
        (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P)) =
    ∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
        (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P') := by
  intro P J₀ P'
  have hm := cavity_rooted_full_replica_transport n K H S b S₀ hS₀ L C
    hbCascade hK hH hS hb hdet hΔ hQ hR hQR π
  have hi := (cavity_rooted_full_integrability n K H S b S₀ hS₀ L C
    hbCascade hK hH hS hb hdet hΔ hQ hR hQR π).mono (fun _ h => h.2)
  have hr := cavity_rooted_replicas_same_root n K (H n) L C π P hi
  let T : (ℕ → CavitySpinState d k n) → ℕ → CavitySpinState d k n :=
    fun σ i => cavityRootedSpinInnovation n K H b (σ i)
  have hT : Measurable T := Measurable.of_eval fun i =>
    (measurable_cavityRootedSpinInnovation n K H b).comp (measurable_pi_apply i)
  have htest := measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a
  rw [← hm, integral_map hT.aemeasurable htest.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hr] with σ hσ
  exact (cavityRootedDepthTest_innovation n K H b hdet a σ hσ).symm

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_rooted_depth_test_transport_oai := @OAI.InvariantIsing.cavity_rooted_depth_test_transport_oai
