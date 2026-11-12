-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_residual_innovation_leaf_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:53.419309+00:00
-- url     : https://prove2.me/submissions/9a6d3124-19ac-4f20-b0ce-ab8272800579

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001
import Definitions.Def_OAIQ258002

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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
-- module Solutions.OAIQ258_II.IsingPerceptron_LintegralGammaKernel
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lintegral Gamma Kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron.Marked

variable {E : Type} [MeasurableSpace E] [Nonempty E]

omit [Nonempty E] in
lemma sigmaPart_eq_of_good (μ : Measure E) [SigmaFinite μ] {ν : Measure E}
    (hν : PoissonGood μ ν) : sigmaPart μ ν = ν := by
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

end IsingPerceptron.Marked

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul]

variable (A : Type) [MeasurableSpace A] [Nonempty A]

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

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma NoiseGibbsRegular.masses {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S} {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞) ∧
      (0 < noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) ∧
        noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) < ∞) := by
  cases n with
  | zero => simp [noiseTreeTotal, rawTreeTotal]
  | succ n => exact ⟨hν.1,hν.2.1⟩

omit [MeasurableSpace A] [MeasurableSpace S] [Nonempty A] in
lemma noiseLeafProduct_telescoping (n : ℕ) (X : ℕ → S → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) :
    noiseLeafProduct n (fun i p => Real.exp (X (i+1) (u i p) - X i p.1)) u s v =
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v - X 0 s)) := by
  induction n generalizing X u s with
  | zero => simp [noiseLeafProduct, noiseLeafTerminal]
  | succ n ih =>
    rw [noiseLeafProduct]
    have hi := ih (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2
    rw [hi]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    change X 1 (u 0 (s,v.2.1)) - X 0 s +
      (noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 -
        X 1 (u 0 (s,v.2.1))) = _
    change _ = noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 - X 0 s
    ring

end IsingPerceptron

namespace IsingPerceptron
lemma normalizeMass_smul_any {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞) :
    normalizeMass (c • ν) = normalizeMass ν := by
  by_cases hν : 0 < ν univ ∧ ν univ < ∞
  · exact normalizeMass_smul ν hc hν
  · have ht : ¬ (0 < (c • ν) univ ∧ (c • ν) univ < ∞) := by
      intro h
      apply hν
      simp only [Measure.smul_apply, smul_eq_mul] at h
      constructor
      · by_contra hh
        have hz : ν univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
        simpa [hz] using h.1
      · rcases ENNReal.mul_lt_top_iff.mp h.2 with hh | hh | hh
        · exact hh.2
        · exact (hc.1.ne' hh).elim
        · simp [hh]
    simp only [normalizeMass, ite_eq_right ht, ite_eq_right hν]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noiseTerminalGibbsLaw_eq_tilted (n : ℕ) {X : ℕ → S → ℝ}
    {u : ℕ → S × A → S} (hX : ∀ i, Measurable (X i))
    (hu : ∀ i, Measurable (u i)) (s : S) (ν : NoiseTree A n) :
    noiseTerminalGibbsLaw n X u s ν = noiseTiltedLeafLaw n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν := by
  have hm : Measurable (noiseLeafProduct n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s) :=
    (measurable_noiseLeafProduct n (fun i => ((hX (i+1) |>.comp (hu i)).sub
      ((hX i).comp measurable_fst)).exp) hu).comp (measurable_const.prodMk measurable_id)
  have hd : (fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v))) =
      ENNReal.ofReal (Real.exp (X 0 s)) • noiseLeafProduct n
        (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, noiseLeafProduct_telescoping]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  unfold noiseTerminalGibbsLaw noiseTiltedLeafLaw
  rw [hd, withDensity_smul _ hm, normalizeMass_smul_any _]
  exact ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top⟩

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma measurable_cavityQuadraticStepWeight {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) :
    Measurable (cavityQuadraticStepWeight K P C ζ) := by
  unfold cavityQuadraticStepWeight
  fun_prop

lemma cavityQuadraticStepWeight_pos {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    0 < cavityQuadraticStepWeight K P C ζ p := Real.exp_pos _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticTree
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma cavityInnovationTree_forget {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTreeForget _ n (cavityInnovationTree n b μ c g s V) =
      noiseTreeForget _ n (noiseTreeKeep n b μ c (fun _ p => p.1 + p.2) s V) := by
  induction n generalizing b μ c g s with
  | zero => rfl
  | succ n ih =>
    let bt := fun i => b (i + 1)
    let μt := fun i => μ (i + 1)
    let ct := fun i => c (i + 1)
    let gt := fun i => g (i + 1)
    let F := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
        cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    let G := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (p.2.1,
        noiseTreeKeep n bt μt ct (fun _ p => p.1 + p.2) (s + p.2.1) p.2.2))
    have hF : Measurable F :=
      (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
        (((hg 0).comp (by fun_prop)).prodMk
          ((measurable_cavityInnovationTree n bt μt ct gt
            (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    have hG : Measurable G :=
      (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
        (measurable_snd.fst.prodMk
          ((measurable_noiseTreeKeep n bt μt (fun i => hc (i + 1))
            (fun _ => measurable_fst.add measurable_snd)).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    change Measure.map (fun p => (p.1, noiseTreeForget _ n p.2.2))
      (Measure.map F _) = Measure.map (fun p => (p.1, noiseTreeForget _ n p.2.2))
        (Measure.map G _)
    have hforget : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        (p.1, noiseTreeForget _ n p.2.2)) :=
      measurable_fst.prodMk ((measurable_noiseTreeForget _ n).comp measurable_snd.snd)
    rw [Measure.map_map hforget hF, Measure.map_map hforget hG]
    congr 1
    funext p
    exact Prod.ext rfl (ih bt μt ct gt (fun i => hc (i + 1)) (fun i => hg (i + 1))
      (s + p.2.1) p.2.2)

lemma cavityInnovationTree_total {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTreeTotal _ n (cavityInnovationTree n b μ c g s V) =
      noiseTreeTotal _ n (noiseTreeKeep n b μ c (fun _ p => p.1 + p.2) s V) := by
  unfold noiseTreeTotal
  rw [cavityInnovationTree_forget n b μ c g hc hg s V]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationKernel
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

theorem cavityInnovationLeaf_unnormalized {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a)) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hV : NoiseGibbsRegular n b μ c (fun _ p => p.1 + p.2) s V)
    (F : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n → ℝ≥0∞) (hF : Measurable F) :
    noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * (∫⁻ v,
      noiseLeafProduct n c (fun _ p => p.1 + p.2) s v *
        F (cavityInnovationLeaf n c g s v) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) *
        ∫⁻ v, F v ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
  induction n generalizing b μ c g s with
  | zero =>
    simp [noiseTreeTotal, rawTreeTotal, cavityInnovationTree,
      noiseLeafProduct, cavityInnovationLeaf, noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j + 1)
    let μt := fun j => μ (j + 1)
    let ct := fun j => c (j + 1)
    let gt := fun j => g (j + 1)
    let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
    have hu : ∀ i, Measurable (u i) := fun _ => measurable_fst.add measurable_snd
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n bt μt : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)))
    let T := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
        cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    have hT : Measurable T :=
      (((hc 0).comp (by fun_prop)).mul measurable_fst).prodMk
        (((hg 0).comp (by fun_prop)).prodMk
          ((measurable_cavityInnovationTree n bt μt ct gt
            (fun j => hc (j + 1)) (fun j => hg (j + 1))).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    have hσ : sigmaPart I V = V := Marked.sigmaPart_eq_of_good I hV.2.2.1
    have hd : ∀ᵐ p ∂V, NoiseGibbsRegular n bt μt ct u (s + p.2.1) p.2.2 := by
      have hh : ∀ᵐ p ∂sigmaPart I V,
          NoiseGibbsRegular n bt μt ct u (s + p.2.1) p.2.2 := hV.2.2.2
      rwa [hσ] at hh
    have htree : cavityInnovationTree (n + 1) b μ c g s V = V.map T := by
      change (sigmaPart I V).map T = _
      rw [hσ]
    have hmass : 0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) (n + 1) (cavityInnovationTree (n + 1) b μ c g s V) ∧
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) (n + 1) (cavityInnovationTree (n + 1) b μ c g s V) < ∞ := by
      rw [cavityInnovationTree_total (n + 1) b μ c g hc hg s V]
      exact hV.masses.2
    have hG : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) (n + 1) =>
        noiseLeafProduct (n + 1) c u s v * F (cavityInnovationLeaf (n + 1) c g s v)) :=
      ((measurable_noiseLeafProduct (n + 1) hc hu).comp
        (measurable_const.prodMk measurable_id)).mul
        (hF.comp ((measurable_cavityInnovationLeaf (n + 1) c g hc hg).comp
          (measurable_const.prodMk measurable_id)))
    rw [noiseLeafKernel_unnormalized_lintegral n V hV.1 hG,
      noiseLeafKernel_unnormalized_lintegral n _ hmass hF, htree]
    have hmF : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        ∫⁻ v, F (p.1, (p.2.1, v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)) ×
          NoiseLeaf (EuclideanSpace ℝ (Fin d)) n => (p.1.1, (p.1.2.1, p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap (fun p :
          ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) => p.2.2)
          (by fun_prop))
    rw [lintegral_map' (show AEMeasurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 *
          ∫⁻ v, F (p.1, (p.2.1, v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) _ from
      (((by fun_prop : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
          ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n).comp measurable_snd.snd)).mul hmF).aemeasurable)
      hT.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with p hp
    have hFp : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
        F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := ih bt μt ct gt (fun j => hc (j + 1)) (fun j => hg (j + 1))
      (fun j => hcpos (j + 1)) (s + p.2.1) p.2.2 hp _ hFp
    change ENNReal.ofReal (max p.1 0) * noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 *
      (∫⁻ v, (ENNReal.ofReal (c 0 (s, p.2.1)) * noiseLeafProduct n ct u (s + p.2.1) v) *
        F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
          cavityInnovationLeaf n ct gt (s + p.2.1) v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) =
      ENNReal.ofReal (max (c 0 (s, p.2.1) * p.1) 0) *
        noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2) *
        (∫⁻ v, F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), v))
          ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    have hcmax : max (c 0 (s, p.2.1) * p.1) 0 = c 0 (s, p.2.1) * max p.1 0 := by
      rw [mul_max_of_nonneg _ _ (hcpos 0 s p.2.1).le, mul_zero]
    rw [hcmax, ENNReal.ofReal_mul (hcpos 0 s p.2.1).le]
    simp_rw [mul_assoc]
    have hz : Measurable (fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
        noiseLeafProduct n ct u (s + p.2.1) v *
          F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
            cavityInnovationLeaf n ct gt (s + p.2.1) v))) :=
      ((measurable_noiseLeafProduct n (fun j => hc (j + 1)) hu).comp
        (measurable_const.prodMk measurable_id)).mul
        (hFp.comp ((measurable_cavityInnovationLeaf n ct gt
          (fun j => hc (j + 1)) (fun j => hg (j + 1))).comp
            (measurable_const.prodMk measurable_id)))
    rw [lintegral_const_mul _ hz]
    calc
      _ = ENNReal.ofReal (c 0 (s, p.2.1)) * ENNReal.ofReal (max p.1 0) *
          (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n p.2.2 * ∫⁻ v, noiseLeafProduct n ct u (s + p.2.1) v *
            F (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
              cavityInnovationLeaf n ct gt (s + p.2.1) v)) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n p.2.2) := by ring
      _ = _ := by rw [he]; ring

theorem cavityInnovationLeaf_tilted_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a)) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hV : NoiseGibbsRegular n b μ c (fun _ p => p.1 + p.2) s V) :
    (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s V).map
      (cavityInnovationLeaf n c g s) =
        noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
  let u := fun (_ : ℕ) (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => p.1 + p.2
  let m := (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc (fun _ => measurable_fst.add measurable_snd)).comp
      (measurable_const.prodMk measurable_id)
  have hk : Measurable (cavityInnovationLeaf n c g s) :=
    (measurable_cavityInnovationLeaf n c g hc hg).comp (measurable_const.prodMk measurable_id)
  have hmass : 0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) ∧
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) < ∞ := by
    rw [cavityInnovationTree_total n b μ c g hc hg s V]
    exact hV.masses.2
  have he : (noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V • m).map (cavityInnovationLeaf n c g s) =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) •
        noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF hk, lintegral_smul_measure, lintegral_smul_measure]
    change noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * (∫⁻ v, F (cavityInnovationLeaf n c g s v)
      ∂(noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).withDensity (noiseLeafProduct n c u s)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hp
      (show Measurable (fun v => F (cavityInnovationLeaf n c g s v)) from hF.comp hk)]
    exact cavityInnovationLeaf_unnormalized n b μ c g hc hg hcpos s V hV F hF
  have hm : noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * m Set.univ =
      noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n (cavityInnovationTree n b μ c g s V) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) => η Set.univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, Set.preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m Set.univ := by
    by_contra hh
    have hz : m Set.univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz, mul_zero] at hm
    exact hmass.1.ne' hm.symm
  have him : m Set.univ < ∞ := by
    have ht : noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V * m Set.univ < ∞ := hm ▸ hmass.2
    rcases ENNReal.mul_lt_top_iff.mp ht with h | h | h
    · exact h.2
    · exact (hV.masses.1.1.ne' h).elim
    · exact (hm0.ne' h).elim
  change (normalizeMass m).map _ = _
  rw [← normalizeMass_smul m hV.masses.1 ⟨hm0, him⟩,
    normalizeMass_map _ hk (by
      simp only [Measure.smul_apply, smul_eq_mul, hm]
      exact hmass), he,
    normalizeMass_smul _ hmass (by simp), normalizeMass_of_probability]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticNormalizer
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

lemma cavityQuadraticStepWeight_telescoping {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (i : ℕ) (s a : EuclideanSpace ℝ (Fin d)) :
    cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i) (s, a) =
      Real.exp (cavityQuadraticValue n K H b (i + 1) (s + a) -
        cavityQuadraticValue n K H b i s) := by
  unfold cavityQuadraticStepWeight cavityQuadraticValue cavityDeterminantStep
  rw [Finset.sum_range_succ]
  congr 1
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticReplica
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint replica sampling after the finite quadratic change of measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityQuadratic_terminalGibbsLaw {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTerminalGibbsLaw n (cavityQuadraticValue n K H b) (fun _ p => p.1 + p.2) s V =
      noiseTiltedLeafLaw n (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun _ p => p.1 + p.2) s V := by
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  rw [noiseTerminalGibbsLaw_eq_tilted n
    (fun i => measurable_cavityQuadraticValue n K H b i) hu s V]
  have he : (fun i (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      Real.exp (cavityQuadraticValue n K H b (i + 1) (p.1 + p.2) -
        cavityQuadraticValue n K H b i p.1)) =
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)) := by
    funext i p
    exact (cavityQuadraticStepWeight_telescoping n K H b i p.1 p.2).symm
  rw [he]

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

theorem cavity_residual_innovation_law {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.PosSemidef)
    (hdet : IsUnit (1 - H * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    ((multivariateGaussian 0 H).tilted (fun z => (1 / 2 : ℝ) *
      ⟪u + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (u + z)⟫)).map
      (fun z => u + z - Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ u) =
      multivariateGaussian 0 (cavityResolvent K H) := by
  have hzero : IsUnit (1 - (0 : Matrix (Fin d) (Fin d) ℝ) * K).det := by simp
  have hΔ : H - 0 = (1 : ℝ) • H := by simp
  have hp : (cavityFactorPrecision
      ((1 : ℝ) • cavityBackwardQuadratic K 0) (CFC.sqrt H)).PosDef := by
    simpa only [cavityBackwardQuadratic_zero, one_smul] using hQ
  simpa only [cavityBackwardQuadratic_zero, zero_mul, sub_zero, inv_one, map_one,
    one_apply_eq_self, Matrix.transpose_one, mul_one, cavityResolvent] using
    cavity_gaussian_step_innovation_law K H 0 H hK (by simp) hH 1 hdet hzero hΔ hp u

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualFinite
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and finiteness of the actual residual-integrated normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

/-- Finiteness of the actual residual partition entails precisely the
backward-quadratic leaf exponential integrability used by its tilted law. -/
lemma cavity_residual_partition_leaf_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hR : R.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt R)).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    Integrable (fun v => Real.exp (⟪cavityLeafSum n s v,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R)
        (cavityLeafSum n s v)⟫ / 2))
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) := by
  let f := fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
    Real.exp (⟪cavityLeafSum n s v,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R)
        (cavityLeafSum n s v)⟫ / 2)
  let c := ENNReal.ofReal (Real.exp (-Real.log (1 - R * K).det / 2))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hm : Measurable f := by
    dsimp [f]
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have he : cavityResidualPartition n K R s V =
      c * ∫⁻ v, ENNReal.ofReal (f v) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V := by
    unfold cavityResidualPartition
    simp_rw [cavity_residual_lintegral K R hK hR hQ, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hL : (∫⁻ v, ENNReal.ofReal (f v)
      ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) < ∞ := by
    rw [he] at hZ
    rcases ENNReal.mul_lt_top_iff.mp hZ with h | h | h
    · exact h.2
    · exact (hc.ne' h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [f, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)] using hL

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary residual, sampled independently for each replica, becomes
independent of the tilted leaf after its centered Gaussian innovation map.
It is not an additional level of the Poisson tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

private lemma cavity_exp_mass_eq_scaled_tilt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (hF : Measurable F) (hI : Integrable (fun x => Real.exp (F x)) μ) :
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (F x))) =
      ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ) • μ.tilted F := by
  have hZ : 0 < ∫ x, Real.exp (F x) ∂μ := integral_exp_pos hI
  rw [Measure.tilted, ← withDensity_smul _ ((hF.exp.div_const _).ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos hZ]
  symm
  calc
    _ = (ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ) *
        (ENNReal.ofReal (∫ x, Real.exp (F x) ∂μ))⁻¹) *
        ENNReal.ofReal (Real.exp (F x)) := by rw [div_eq_mul_inv]; ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hZ).ne'
      ENNReal.ofReal_ne_top, one_mul]

private lemma cavity_weighted_product_transport {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure X) (μ : Measure Y) (κ : Measure Z) [SFinite ν] [SFinite μ] [SFinite κ]
    (w : X × Y → ℝ≥0∞) (a : X → ℝ≥0∞) (T : X × Y → Z)
    (hw : Measurable w) (ha : Measurable a) (hT : Measurable T)
    (hlaw : ∀ x, (μ.withDensity (fun y => w (x, y))).map (fun y => T (x, y)) = a x • κ) :
    ((ν.prod μ).withDensity w).map (fun p => (p.1, T p)) =
      (ν.withDensity a).prod κ := by
  have hmap : Measurable (fun p : X × Y => (p.1, T p)) := measurable_fst.prodMk hT
  apply Measure.ext_of_lintegral
  intro f hf
  have hfc : Measurable (fun p : X × Y => f (p.1, T p)) := hf.comp hmap
  rw [lintegral_map hf hmap, lintegral_withDensity_eq_lintegral_mul _ hw hfc]
  change (∫⁻ p, w p * f (p.1, T p) ∂ν.prod μ) = _
  rw [lintegral_prod _ (show AEMeasurable (fun p : X × Y => w p * f (p.1, T p)) _ from
      (hw.mul hfc).aemeasurable), lintegral_prod _ hf.aemeasurable]
  have hx (x : X) : (∫⁻ y, w (x, y) * f (x, T (x, y)) ∂μ) =
      a x * ∫⁻ z, f (x, z) ∂κ := by
    have hfx : Measurable (fun z => f (x, z)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hTx : Measurable (fun y => T (x, y)) :=
      hT.comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫⁻ y, f (x, T (x, y)) ∂μ.withDensity (fun y => w (x, y)) :=
        (lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (fun y => w (x, y)) from
            hw.comp (measurable_const.prodMk measurable_id))
          (show Measurable (fun y => f (x, T (x, y))) from hfx.comp hTx)).symm
      _ = ∫⁻ z, f (x, z) ∂(μ.withDensity (fun y => w (x, y))).map (fun y => T (x, y)) :=
        (lintegral_map hfx hTx).symm
      _ = _ := by rw [hlaw x, lintegral_smul_measure]; rfl
  simp_rw [hx]
  exact (lintegral_withDensity_eq_lintegral_mul _ ha hf.lintegral_prod_right').symm

private lemma cavity_normalize_prod_right {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
    (ν : Measure X) (κ : Measure Y) [SFinite ν] [IsProbabilityMeasure κ]
    (hν : 0 < ν Set.univ ∧ ν Set.univ < ∞) :
    normalizeMass (ν.prod κ) = (normalizeMass ν).prod κ := by
  have hm : ν.prod κ Set.univ = ν Set.univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      show κ Set.univ = 1 from measure_univ, mul_one]
  rw [normalizeMass, hm, ite_eq_left hν, normalizeMass, ite_eq_left hν,
    Measure.prod_smul_left]

/-- The full leaf/residual Gibbs law factors after centering the ordinary
residual. The first factor is the backward-quadratic leaf tilt, while the
second is a Gaussian with covariance `(I-HK)⁻¹H`. -/
theorem cavity_residual_joint_kernel {X : Type*} [MeasurableSpace X] [Nonempty X]
    {d : ℕ} (ν : Measure X) [IsProbabilityMeasure ν]
    (y : X → EuclideanSpace ℝ (Fin d)) (hy : Measurable y)
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.PosSemidef)
    (hdet : IsUnit (1 - H * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt H)).PosDef)
    (hI : Integrable (fun x => Real.exp
      (⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2)) ν) :
    (normalizeMass ((ν.prod (multivariateGaussian 0 H)).withDensity
      (fun p : X × EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
        (Real.exp (⟪y p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y p.1 + p.2)⟫ / 2))))).map
        (fun p => (p.1, y p.1 + p.2 -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ (y p.1))) =
      (ν.tilted (fun x =>
        ⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2)).prod
          (multivariateGaussian 0 (cavityResolvent K H)) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) H
  let κ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (cavityResolvent K H)
  let F : X → ℝ := fun x =>
    ⟪y x, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K H) (y x)⟫ / 2
  let c : ℝ := -Real.log (1 - H * K).det / 2
  let Q : X × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
    ⟪y p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y p.1 + p.2)⟫ / 2
  let T : X × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun p =>
    y p.1 + p.2 - Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H * K)⁻¹ (y p.1)
  let a : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (c + F x))
  let η := ν.withDensity a
  let M := (ν.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (Q p)))
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hQm : Measurable Q := by dsimp [Q]; fun_prop
  have hTm : Measurable T := by dsimp [T]; fun_prop
  have ham : Measurable a := ((measurable_const.add hFm).exp).ennreal_ofReal
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hlaw (x : X) :
      (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (Q (x, z))))).map (fun z => T (x, z)) =
        a x • κ := by
    have hi := cavity_multivariate_gaussian_integrable K H hKh hQ (y x)
    have he := cavity_exp_mass_eq_scaled_tilt μ (fun z => Q (x, z))
      (hQm.comp (measurable_const.prodMk measurable_id)) hi
    have hTx : Measurable (fun z => T (x, z)) :=
      hTm.comp (measurable_const.prodMk measurable_id)
    rw [he, Measure.map_smul]
    have ht := cavity_residual_innovation_law K H hK hH hdet hQ (y x)
    have hz := cavity_residual_integral K H hKh hH hQ (y x)
    have hf : (fun z : EuclideanSpace ℝ (Fin d) => (1 / 2 : ℝ) *
        ⟪y x + z, Matrix.toEuclideanCLM (𝕜 := ℝ) K (y x + z)⟫) =
        (fun z => Q (x, z)) := by
      funext z
      dsimp [Q]
      ring
    rw [hf] at ht
    change (μ.tilted (fun z => Q (x, z))).map (fun z => T (x, z)) = κ at ht
    rw [ht]
    congr 1
    exact congrArg ENNReal.ofReal hz
  have htransport : M.map (fun p => (p.1, T p)) = η.prod κ :=
    cavity_weighted_product_transport ν μ κ _ a T hQm.exp.ennreal_ofReal ham hTm hlaw
  have hη : η = ENNReal.ofReal (Real.exp c) •
      ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x))) := by
    dsimp only [η]
    rw [← withDensity_smul _ hFm.exp.ennreal_ofReal]
    congr 1
    funext x
    simp only [a, Real.exp_add, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hbase : 0 < (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x)))) Set.univ ∧
      (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (F x)))) Set.univ < ∞ := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
    exact ⟨ENNReal.ofReal_pos.mpr (integral_exp_pos hI), ENNReal.ofReal_lt_top⟩
  have hηmass : 0 < η Set.univ ∧ η Set.univ < ∞ := by
    rw [hη, Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos c)).ne' hbase.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase.2⟩
  have hm : M Set.univ = η Set.univ := by
    have he := congrArg (fun ρ : Measure (X × EuclideanSpace ℝ (Fin d)) => ρ Set.univ) htransport
    rw [Measure.map_apply (measurable_fst.prodMk hTm) MeasurableSet.univ,
      Set.preimage_univ] at he
    have hprod : (η.prod κ) Set.univ = η Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod,
        show κ Set.univ = 1 from measure_univ, mul_one]
    rw [hprod] at he
    exact he
  change (normalizeMass M).map (fun p => (p.1, T p)) = (ν.tilted F).prod κ
  rw [normalizeMass_map M (measurable_fst.prodMk hTm) (hm ▸ hηmass), htransport,
    cavity_normalize_prod_right η κ hηmass, hη,
    normalizeMass_smul _ ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos c), ENNReal.ofReal_lt_top⟩ hbase,
    normalizeMass_exp ν F hFm hI]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualLeafLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual factorization for the actual finite quadratic cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

/-- For every tree with finite actual normalizer, integrating and centering
its ordinary residual leaves the precise quadratic tilted leaf law. -/
theorem cavity_quadratic_residual_leaf_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞) :
    (normalizeMass (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
      (multivariateGaussian 0 (H n))).withDensity
        (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
            Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))))).map
      (fun p => (p.1, cavityLeafSum n s p.1 + p.2 -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
      (noiseTiltedLeafLaw n
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun _ p => p.1 + p.2) s V).prod
          (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  let ν := noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V
  let F := fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
    ⟪cavityLeafSum n s v, Matrix.toEuclideanCLM (𝕜 := ℝ)
      (cavityBackwardQuadratic K (H n)) (cavityLeafSum n s v)⟫ / 2
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hI : Integrable (fun v => Real.exp (F v)) ν :=
    cavity_residual_partition_leaf_integrable n K (H n) hKh hR hQ s V hZ
  have hFm : Measurable F := by
    dsimp [F]
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have hterminal : noiseLeafTerminal n (cavityQuadraticValue n K H b)
      (fun _ p => p.1 + p.2) s = F := by
    funext v
    rw [cavity_noiseLeafTerminal_sum, cavityQuadraticValue_terminal]
  have he : ν.tilted F = noiseTiltedLeafLaw n
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V := by
    rw [← cavityQuadratic_terminalGibbsLaw n K H b s V,
      noiseTerminalGibbsLaw, hterminal]
    exact (normalizeMass_exp ν F hFm hI).symm
  have h := cavity_residual_joint_kernel ν (cavityLeafSum n s) (measurable_cavityLeafSum n s)
    K (H n) hK hR hdet hQ hI
  change _ = (ν.tilted F).prod (multivariateGaussian 0 (cavityResolvent K (H n))) at h
  rw [he] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualInnovation
attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

/-- At every regular tree the transformed leaf and centered terminal
residual are independent, with the leaf law of the innovation tree. -/
theorem cavity_residual_innovation_leaf_law_oai {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V) :
    (cavityQuadraticResidualGibbs n K (H n) s V).map
      (fun p => (cavityInnovationLeaf n
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
        cavityLeafSum n s p.1 + p.2 -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
        (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
  let L := cavityInnovationLeaf n c g s
  let R := fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) =>
    (p.1, cavityLeafSum n s p.1 + p.2 -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hg : ∀ i, Measurable (g i) := fun i => measurable_cavityStepInnovation _ _ _
  have hL : Measurable L := (measurable_cavityInnovationLeaf n c g hc hg).comp
    (measurable_const.prodMk measurable_id)
  have hRmap : Measurable R := by
    have hs := measurable_cavityLeafSum n s
    dsimp [R]
    fun_prop
  have he := cavity_quadratic_residual_leaf_law n K H b hK hR hdet hQ s V hZ
  change (cavityQuadraticResidualGibbs n K (H n) s V).map R = _ at he
  change (cavityQuadraticResidualGibbs n K (H n) s V).map ((Prod.map L id) ∘ R) = _
  rw [← Measure.map_map (hL.prodMap measurable_id) hRmap, he,
    ← Measure.map_prod_map _ _ hL measurable_id, Measure.map_id]
  rw [cavityInnovationLeaf_tilted_law n b (cavityGaussianMarks S) c g hc hg
    (fun i u a => cavityQuadraticStepWeight_pos _ _ _ _ (u, a)) s V hV]

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_residual_innovation_leaf_law_oai := @OAI.InvariantIsing.cavity_residual_innovation_leaf_law_oai
