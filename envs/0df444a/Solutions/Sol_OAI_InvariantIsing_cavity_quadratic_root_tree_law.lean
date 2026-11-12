-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_quadratic_root_tree_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:51.708343+00:00
-- url     : https://prove2.me/submissions/72a1a96f-4ff9-4d1b-8ec5-e64c7ba4844f

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
-- module Solutions.OAIQ258_II.IsingPerceptron_PoissonCloud
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
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

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)



lemma sigmaPart_eq_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, sigmaPart μ ν = ν := by
  have ha : ∀ n, ∀ᵐ ν ∂poissonLaw μ,
      ν (disjointed (spanningSets μ) n) < ∞ := by
    intro n
    have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    apply ae_lt_top (Measure.measurable_coe hm)
    rw [poissonLaw_mean_count μ hm]
    exact ((measure_mono (disjointed_subset _ _)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  filter_upwards [ae_all_iff.mpr ha] with ν hν
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

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
-- module Solutions.OAIQ258_II.IsingPerceptron_MapWithDensityEquiv
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.powerIntensity_nullSingleton _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma cavity_map_powerIntensity_innovation {d n : ℕ} (b : ℝ)
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (P Q : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    (c : EuclideanSpace ℝ (Fin d) → ℝ) (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (T : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) (hT : Measurable T)
    (hLaw : ∀ a, (P : Measure _).map (fun v => T (a, v)) = (Q : Measure _))
    (hν : ((μ : Measure _).withDensity (fun a => ENNReal.ofReal (c a ^ b))).map g =
      (ν : Measure _)) :
    ((powerIntensity b).prod ((μ : Measure _).prod (P : Measure _))).map
      (fun p => (c p.2.1 * p.1, (g p.2.1, T p.2))) =
      (powerIntensity b).prod ((ν : Measure _).prod (Q : Measure _)) := by
  let F := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
    (c p.2.1 * p.1, (g p.2.1, T p.2))
  have hF : Measurable F := by fun_prop
  have hw : Measurable (fun a => ENNReal.ofReal (c a ^ b)) := (hc.pow_const b).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod (fun p => f (F p)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ v, f (c a * x, (g a, T (a, v))) ∂(P : Measure _)) =
      ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (by fun_prop)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) :
      (∫⁻ p, f (F (x, p)) ∂((μ : Measure _).prod (P : Measure _))) =
      ∫⁻ a, ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) ∂(μ : Measure _) := by
    rw [lintegral_prod (fun p => f (F (x, p)))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    exact lintegral_congr fun a => hv x a
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ w, f (c p.2 * p.1, (g p.2, w)) ∂(Q : Measure _)) :=
    (hf.comp (by fun_prop : Measurable (fun p :
      (ℝ × EuclideanSpace ℝ (Fin d)) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (c p.1.2 * p.1.1, (g p.1.2, p.2))))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ x, ∫⁻ w, f (c a * x, (g a, w)) ∂(Q : Measure _) ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) *
        ∫⁻ x, ∫⁻ w, f (x, (g a, w)) ∂(Q : Measure _) ∂powerIntensity b := by
    have hfa : Measurable (fun x : ℝ =>
        ∫⁻ w, f (x, (g a, w)) ∂(Q : Measure _)) :=
      (hf.comp (by fun_prop : Measurable (fun p :
        ℝ × NoiseTree (EuclideanSpace ℝ (Fin d)) n => (p.1, (g a, p.2))))).lintegral_prod_right'
    rw [← lintegral_map hfa (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  let H := fun a : EuclideanSpace ℝ (Fin d) =>
    ∫⁻ x, ∫⁻ w, f (x, (a, w)) ∂(Q : Measure _) ∂powerIntensity b
  have hH : Measurable H :=
    ((hf.comp (by fun_prop : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × ℝ) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (p.1.2, (p.1.1, p.2))))).lintegral_prod_right').lintegral_prod_right'
  change (∫⁻ a, ENNReal.ofReal (c a ^ b) * H (g a) ∂(μ : Measure _)) = _
  have hden := lintegral_withDensity_eq_lintegral_mul (μ : Measure _) hw (hH.comp hg)
  change (∫⁻ a, H (g a) ∂(μ : Measure _).withDensity
    (fun a => ENNReal.ofReal (c a ^ b))) =
    (∫⁻ a, ENNReal.ofReal (c a ^ b) * H (g a) ∂(μ : Measure _)) at hden
  rw [← hden, ← lintegral_map hH hg, hν]
  change (∫⁻ a, ∫⁻ x, ∫⁻ w, f (x, (a, w)) ∂(Q : Measure _)
    ∂powerIntensity b ∂(ν : Measure _)) = _
  rw [lintegral_lintegral_swap]
  · rw [lintegral_prod _ hf.aemeasurable]
    apply lintegral_congr
    intro x
    exact (lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
  · exact ((hf.comp (by fun_prop : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × ℝ) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        (p.1.2, (p.1.1, p.2))))).lintegral_prod_right').aemeasurable

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

/-- If the retained innovation has the same law at every ancestor,
the full transformed tree has independent marks with that law. -/
theorem cavityInnovationTree_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a))
    (hν : ∀ i s, (((μ i : Measure _).withDensity
      (fun a => ENNReal.ofReal (c i (s, a) ^ b i))).map (fun a => g i (s, a))) =
        (ν i : Measure _)) (s : EuclideanSpace ℝ (Fin d)) :
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _).map
      (cavityInnovationTree n b μ c g s) = noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b ν := by
  induction n generalizing b μ ν c g s with
  | zero => exact Measure.map_dirac' measurable_const _
  | succ n ih =>
      let b' := fun i => b (i + 1)
      let μ' := fun i => μ (i + 1)
      let ν' := fun i => ν (i + 1)
      let c' := fun i => c (i + 1)
      let g' := fun i => g (i + 1)
      let P : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
        noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b' μ'
      let Q : ProbabilityMeasure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
        noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b' ν'
      let I := (powerIntensity (b 0)).prod ((μ 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
        (P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)))
      let T := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
        cavityInnovationTree n b' μ' c' g' (s + p.1) p.2
      have hT : Measurable T :=
        (measurable_cavityInnovationTree n b' μ' c' g'
          (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
            ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have hLaw (a : EuclideanSpace ℝ (Fin d)) :
          (P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)).map (fun v => T (a, v)) =
            (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)) :=
        ih b' μ' ν' c' g' (fun i => hc (i + 1)) (fun i => hg (i + 1))
          (fun i => hcpos (i + 1)) (fun i => hν (i + 1)) (s + a)
      let G := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1), T p.2))
      have hG : Measurable G := by
        exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
          (((hg 0).comp (by fun_prop)).prodMk (hT.comp measurable_snd))
      have hI : I.map G = (powerIntensity (b 0)).prod ((ν 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
          (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))) :=
        cavity_map_powerIntensity_innovation (b 0) (μ 0) (ν 0) P Q
          (fun a => c 0 (s, a)) ((hc 0).comp (measurable_const.prodMk measurable_id))
          (hcpos 0 s) (fun a => g 0 (s, a))
          ((hg 0).comp (measurable_const.prodMk measurable_id)) T hT hLaw (hν 0 s)
      rw [noiseCascadeLaw_succ, noiseCascadeLaw_succ]
      change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod
        ((ν 0 : Measure (EuclideanSpace ℝ (Fin d))).prod
          (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))))
      calc
        _ = (poissonLaw I).map (fun V => V.map G) := by
          apply Measure.map_congr
          filter_upwards [sigmaPart_eq_ae I] with V hV
          change (sigmaPart I V).map G = V.map G
          rw [hV]
        _ = poissonLaw (I.map G) := poissonLaw_map I hG
        _ = _ := poissonLaw_congr hI

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

lemma measurable_cavityQuadraticStepWeight {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) :
    Measurable (cavityQuadraticStepWeight K P C ζ) := by
  unfold cavityQuadraticStepWeight
  fun_prop

lemma cavityQuadraticStepWeight_pos {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    0 < cavityQuadraticStepWeight K P C ζ p := Real.exp_pos _

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

/-- Actual backward quadratic weights turn the finite Gaussian tree
into a tree with independent centered Gaussian innovations. -/
theorem cavity_quadratic_innovation_tree_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (u : EuclideanSpace ℝ (Fin d)) :
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _).map
      (cavityInnovationTree n b (cavityGaussianMarks S)
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun i => cavityStepInnovation K (H i) (H (i + 1))) u) =
      noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) := by
  apply cavityInnovationTree_law
  · intro i
    exact measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  · intro i
    exact measurable_cavityStepInnovation K (H i) (H (i + 1))
  · intro i s a
    exact cavityQuadraticStepWeight_pos K (H i) (H (i + 1)) (b i) (s, a)
  · intro i s
    exact cavity_quadratic_step_weight_innovation_law K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1))
      (hΔ i) (hQ i) s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootInnovationLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence of the common Gaussian root and retained innovation tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma cavity_root_tree_independent {d : ℕ} (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (P Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [SFinite μ] [SFinite P] [SFinite Q]
    (R : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hR : Measurable R)
    (T : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) (hT : Measurable T)
    (hPQ : ∀ s, P.map (fun V => T (s, V)) = Q) :
    (μ.prod P).map (fun p => (R p.1, T p)) = (μ.map R).prod Q := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hmap : Measurable (fun p : EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n => (R p.1, T p)) :=
    (hR.comp measurable_fst).prodMk hT
  rw [lintegral_map hF hmap,
    lintegral_prod (fun p : EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n => F (R p.1, T p))
      (show AEMeasurable (fun p => F (R p.1, T p)) (μ.prod P) from
        (hF.comp hmap).aemeasurable),
    lintegral_prod _ hF.aemeasurable]
  have hinner (s : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ V, F (R s, T (s, V)) ∂P) = ∫⁻ V, F (R s, V) ∂Q := by
    rw [← hPQ s, lintegral_map
      (show Measurable (fun V => F (R s, V)) from
        hF.comp (measurable_const.prodMk measurable_id))
      (show Measurable (fun V => T (s, V)) from
        hT.comp (measurable_const.prodMk measurable_id))]
  simp_rw [hinner]
  exact (lintegral_map hF.lintegral_prod_right' hR).symm

/-- Root-dependent reweighting preserves the unchanged external root law.
After the deterministic root rescaling, the innovation tree is independent
of a centered Gaussian root with covariance `J₀ S₀ J₀ᵀ`. -/
theorem cavity_quadratic_root_tree_law_oai {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef) :
    let μ := cavityGaussianMarks S
    let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
    let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
    let J := (1 - H 0 * K)⁻¹
    ((multivariateGaussian 0 S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)).map
        (fun p => (Matrix.toEuclideanCLM (𝕜 := ℝ) J p.1,
          cavityInnovationTree n b μ c g p.1 p.2)) =
      (multivariateGaussian 0 (J * S₀ * J.transpose)).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _) := by
  dsimp only
  rw [cavity_root_tree_independent n
    (multivariateGaussian 0 S₀)
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks (fun i =>
      (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹) (by fun_prop)
    (fun p => cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) p.1 p.2)
    (measurable_cavityInnovationTree n b (cavityGaussianMarks S) _ _
      (fun i => measurable_cavityQuadraticStepWeight _ _ _ _)
      (fun i => measurable_cavityStepInnovation _ _ _))
    (fun s => cavity_quadratic_innovation_tree_law n K H S b hK hH hS hb hdet hΔ hQ s)]
  congr 1
  simpa only [map_zero, zero_add] using
    cavity_multivariateGaussian_affine_image (1 - H 0 * K)⁻¹ S₀ hS₀ 0 0

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_quadratic_root_tree_law_oai := @OAI.InvariantIsing.cavity_quadratic_root_tree_law_oai
