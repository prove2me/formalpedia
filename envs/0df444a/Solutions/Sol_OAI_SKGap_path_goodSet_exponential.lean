-- Prove2me | solution 1 for OAI.SKGap.path_goodSet_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:34.73817+00:00
-- url     : https://prove2.me/submissions/630a9584-5052-4714-903a-d741cb126177

import Mathlib
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Quadratic
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
namespace SKGap.ComplexSpectral
variable {ι : Type*} [Fintype ι]

lemma lowerRayleigh_ge [Nonempty ι] {M : Matrix ι ι ℂ} {c : ℝ}
    (hc : ∀ x ∈ unitSphere ι, c ≤ quadratic M x) : c ≤ lowerRayleigh M := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hn : (quadratic M '' unitSphere ι).Nonempty := by
    refine ⟨quadratic M (EuclideanSpace.single i (1:ℂ)),?_⟩
    exact ⟨_,by simp [unitSphere],rfl⟩
  exact le_csInf hn (by rintro _ ⟨x,hx,rfl⟩; exact hc x hx)

end SKGap.ComplexSpectral

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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StandardGaussianProduct
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

theorem continuous_insertNth {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℝ) :
    Continuous (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simp only [Fin.insertNth_apply_same]
    convert! (continuous_id : Continuous (fun x : ℝ => x)) using 1
  · intro k
    simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_const : Continuous (fun _ : ℝ => u k))

theorem gaussianProduct_coordinate_IBP {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hdf : Continuous df)
    (hfbound : ∀ x, ‖f x‖ ≤ C) (hdfbound : ∀ x, ‖df x‖ ≤ D)
    (hder : ∀ (u : Fin n → ℝ) (z : ℝ),
      HasDerivAt (fun z => f (i.insertNth z u)) (df (i.insertNth z u)) z) :
    (∫ x, x i * f x ∂standardGaussianProduct (n + 1)) =
      ∫ x, df x ∂standardGaussianProduct (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n + 1) → ℝ => x i * f x)
      (standardGaussianProduct (n + 1)) := by
    simpa only [mul_comm, standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.aestronglyMeasurable (ae_of_all _ hfbound)
  have hi' : Integrable df (standardGaussianProduct (n + 1)) :=
    Integrable.of_bound hdf.aestronglyMeasurable D (ae_of_all _ hdfbound)
  have hsplit (g : (Fin (n + 1) → ℝ) → ℝ)
      (hg : Integrable g (standardGaussianProduct (n + 1))) :
      (∫ x, g x ∂standardGaussianProduct (n + 1)) =
        ∫ u, ∫ z, g (i.insertNth z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) :=
      hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g, integral_prod _ hi2]
    rw [integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi, hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Fin.insertNth_apply_same]
  have hfu : Integrable (fun z => f (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hf.comp (continuous_insertNth i u)).aestronglyMeasurable C
      (ae_of_all _ (fun z => hfbound _))
  have hdfu : Integrable (fun z => df (i.insertNth z u)) (gaussianReal 0 1) :=
    Integrable.of_bound (hdf.comp (continuous_insertNth i u)).aestronglyMeasurable D
      (ae_of_all _ (fun z => hdfbound _))
  have hzfu : Integrable (fun z => z * f (i.insertNth z u)) (gaussianReal 0 1) := by
    simpa only [mul_comm, id_eq, Function.comp_def] using (IsGaussian.integrable_id (μ := gaussianReal 0 1)).bdd_mul
      (hf.comp (continuous_insertNth i u)).aestronglyMeasurable
      (ae_of_all _ (fun z => hfbound _))
  simpa only [NNReal.coe_one, sub_zero, one_mul] using
    gaussian_integration_by_parts (d := 0) (s := 1) one_ne_zero (hder u) hfu hdfu
      (by simpa only [sub_zero] using hzfu)

end SKGap

open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiftMatrix
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
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma vec_norm_split (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 = ‖reVec x‖^2+‖imVec x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ‖x i‖^2 = ‖(x i).re‖^2+‖(x i).im‖^2
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Real.norm_eq_abs]
  rw [sq_abs,sq_abs]
  ring

omit [DecidableEq ι] in
lemma norm_liftVec (x : EuclideanSpace ℝ ι) : ‖liftVec x‖ = ‖x‖ := by
  have hh : ‖liftVec x‖^2 = ‖x‖^2 := by simp [EuclideanSpace.norm_sq_eq,liftVec]
  nlinarith [norm_nonneg (liftVec x),norm_nonneg x]

lemma reVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    reVec (clin (liftMatrix M) x) = rlin M (reVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).re = ∑ j, M i j*(x j).re
  simp

lemma imVec_clin (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    imVec (clin (liftMatrix M) x) = rlin M (imVec x) := by
  ext i
  change (∑ j, (M i j : ℂ)*x j).im = ∑ j, M i j*(x j).im
  simp

lemma clin_liftVec (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    clin (liftMatrix M) (liftVec x) = liftVec (rlin M x) := by
  ext i
  change (∑ j, (M i j : ℂ)*(x j : ℂ)) = ((∑ j, M i j*x j : ℝ) : ℂ)
  simp

lemma operator_norm_lift (M : Matrix ι ι ℝ) : ‖clin (liftMatrix M)‖ = opNorm M := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [← sq]
    change ‖clin (liftMatrix M) x‖^2 ≤ (opNorm M*‖x‖)^2
    rw [vec_norm_split,reVec_clin,imVec_clin,mul_pow,vec_norm_split,mul_add]
    have hr := (rlin M).le_opNorm (reVec x)
    have hi := (rlin M).le_opNorm (imVec x)
    change ‖rlin M (reVec x)‖ ≤ opNorm M*‖reVec x‖ at hr
    change ‖rlin M (imVec x)‖ ≤ opNorm M*‖imVec x‖ at hi
    nlinarith [norm_nonneg (rlin M (reVec x)),norm_nonneg (rlin M (imVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (reVec x)),
      mul_nonneg (norm_nonneg (rlin M)) (norm_nonneg (imVec x))]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hh := (clin (liftMatrix M)).le_opNorm (liftVec x)
    rwa [clin_liftVec,norm_liftVec,norm_liftVec] at hh

end SKGap.RealComplex

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealQuadratic
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
namespace SKGap.RealComplex
open SKGap.ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_lift_split (M : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    quadratic (liftMatrix M) x = realQuadratic M (reVec x)+realQuadratic M (imVec x) := by
  change (∑ i, star (x i)*∑ k, (M i k:ℂ)*x k).re = _
  simp only [Finset.mul_sum,Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realQuadratic,reVec,imVec,PiLp.toLp_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma lowerRayleigh_lift_ge [Nonempty ι] {M : Matrix ι ι ℝ} {c : ℝ}
    (hc : ∀ x : EuclideanSpace ℝ ι, c*‖x‖^2 ≤ realQuadratic M x) :
    c ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix M) := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  have h := add_le_add (hc (reVec x)) (hc (imVec x))
  rw [← mul_add,← vec_norm_split,hn,one_pow,mul_one,← quadratic_lift_split] at h
  exact h

lemma quadratic_eq_inner (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadratic M x = (inner ℂ x (clin M x)).re := by
  rw [PiLp.inner_apply]
  change (∑ i, star (x i)*(∑ k, M i k*x k)).re =
    (∑ i, (∑ k, M i k*x k)*star (x i)).re
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lowerRayleigh_ge_neg_norm [Nonempty ι] (M : Matrix ι ι ℂ) :
    -‖clin M‖ ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh M := by
  apply lowerRayleigh_ge
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [unitSphere,Metric.mem_sphere,dist_zero_right] using hx
  rw [quadratic_eq_inner]
  have hh := (norm_inner_le_norm (𝕜 := ℂ) x (clin M x)).trans
    (mul_le_mul_of_nonneg_left ((clin M).le_opNorm x) (norm_nonneg x))
  rw [hn,mul_one,one_mul] at hh
  exact (neg_le_neg ((Complex.abs_re_le_norm _).trans hh)).trans (neg_abs_le _)

lemma lowerRayleigh_neg_lift_ge [Nonempty ι] (M : Matrix ι ι ℝ) :
    -opNorm M ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix M) := by
  have h := lowerRayleigh_ge_neg_norm (-liftMatrix M)
  have he : clin (-liftMatrix M) = -clin (liftMatrix M) := by
    ext x i
    change (∑ k, -(liftMatrix M i k)*x k) = -(∑ k, liftMatrix M i k*x k)
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [he,norm_neg,operator_norm_lift] at h
  exact h

end SKGap.RealComplex

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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LipschitzNormedConvolution
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
namespace SKGap

section Smoothing
open NormedSpace
open scoped Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lipschitz_normed_convolution {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (φ : ContDiffBump (0 : E))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    LipschitzWith L (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hcv : ConvolutionExists (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed
      (hf.continuous.locallyIntegrable (μ := μ))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hx : Integrable (fun t => φ.normed μ t * f (x - t)) μ := hcv x
  have hy : Integrable (fun t => φ.normed μ t * f (y - t)) μ := hcv y
  rw [← integral_sub hx hy]
  calc
    _ ≤ ∫ t, φ.normed μ t * ((L : ℝ) * ‖x - y‖) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (φ.normed μ t),
        abs_of_nonneg (φ.nonneg_normed _)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed _)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (x - t) (y - t)
    _ = (L : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem exists_smooth_lipschitz_approx {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, dist (g x) (f x) ≤ (L : ℝ) * ε := by
  let μ : Measure E := addHaar
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let g := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  refine ⟨g, ?_, lipschitz_normed_convolution hf φ μ, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply ContDiffBump.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    apply (hf.dist_le_mul y x).trans
    exact mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg

end Smoothing

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [IsGaussian μ]

theorem gaussian_integrable_exp_norm (a : ℝ) :
    Integrable (fun x : E => exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hI.const_mul (exp (a ^ 2 / (4 * C)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hs := sq_nonneg (‖x‖ - a / (2 * C))
  have hC0 : C ≠ 0 := ne_of_gt hC
  have heq : C * (‖x‖ - a / (2 * C)) ^ 2 =
      C * ‖x‖ ^ 2 - a * ‖x‖ + a ^ 2 / (4 * C) := by field_simp; ring
  nlinarith [mul_nonneg (le_of_lt hC) hs]

end GaussianMoments

section StandardGaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_map_dual (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (Real.toNNReal (‖L‖ ^ 2)) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]

theorem stdGaussian_integral_exp_dual (L : StrongDual ℝ E) (r : ℝ) :
    (∫ x, exp (r * L x) ∂stdGaussian E) = exp (r ^ 2 * ‖L‖ ^ 2 / 2) := by
  have hm := mgf_gaussianReal
    (stdGaussian_map_dual L) r
  simpa [mgf, Real.toNNReal_of_nonneg (sq_nonneg _), mul_div_assoc, mul_comm] using hm

theorem gaussian_integrable_exp_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun x => exp (r * f x)) μ := by
  have hfc := hf.continuous
  have hI := (gaussian_integrable_exp_norm (μ := μ) (|r| * L)).const_mul
    (exp (|r| * |f 0|))
  apply hI.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  have hx : |f x| ≤ |f 0| + L * ‖x‖ := by
    have hh := hf.norm_sub_le x 0
    simp only [sub_zero, Real.norm_eq_abs] at hh
    have ht := abs_add_le (f x - f 0) (f 0)
    rw [sub_add_cancel] at ht
    linarith
  calc
    r * f x ≤ |r * f x| := le_abs_self _
    _ = |r| * |f x| := abs_mul _ _
    _ ≤ |r| * (|f 0| + L * ‖x‖) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by ring

theorem gaussian_integrable_lipschitz {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) : Integrable f μ := by
  have hI := ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (L : ℝ)).add
    (integrable_const |f 0|)
  apply hI.mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  change |f x| ≤ (L : ℝ) * ‖x‖ + |f 0|
  have hh := hf.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at hh ⊢
  have ht := abs_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at ht
  linarith

end StandardGaussian

theorem exp_interval_average_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) :
    exp (a⁻¹ * ∫ t in (0 : ℝ)..a, g t) ≤
      a⁻¹ * ∫ t in (0 : ℝ)..a, exp (g t) := by
  have h0 : volume (Icc (0 : ℝ) a) ≠ 0 := by
    rw [volume_Icc, sub_zero, ENNReal.ofReal_ne_zero_iff]
    exact ha
  have ht : volume (Icc (0 : ℝ) a) ≠ ∞ := by simp
  have hJ := convexOn_exp.map_set_average_le continuous_exp.continuousOn isClosed_univ
    h0 ht (by filter_upwards [] with x; exact mem_univ _)
    hg.integrableOn_Icc (continuous_exp.comp hg).integrableOn_Icc
  have hvol : volume.real (Icc (0 : ℝ) a) = a := by
    simp [measureReal_def, volume_Icc, ha.le]
  simpa only [setAverage_eq, hvol, smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le] using hJ

section Rotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rotation_snd_norm_le (θ : ℝ) (p : E × E) :
    ‖(ContinuousLinearMap.rotation θ p).2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [ContinuousLinearMap.rotation_apply]
  calc
    ‖-sin θ • p.1 + cos θ • p.2‖ ≤ ‖-sin θ • p.1‖ + ‖cos θ • p.2‖ := norm_add_le _ _
    _ = |sin θ| * ‖p.1‖ + |cos θ| * ‖p.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖p.1‖ + 1 * ‖p.2‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (abs_sin_le_one _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by ring

theorem hasDerivAt_rotation_fst (θ : ℝ) (p : E × E) :
    HasDerivAt (fun t => (ContinuousLinearMap.rotation t p).1)
      (ContinuousLinearMap.rotation θ p).2 θ := by
  exact ((hasDerivAt_cos θ).smul_const p.1).add
    ((hasDerivAt_sin θ).smul_const p.2)

theorem rotation_fundamental_theorem {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (p : E × E) :
    (∫ θ in (0 : ℝ)..π / 2,
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) =
        f p.2 - f p.1 := by
  have hd : ∀ θ, HasDerivAt (fun t => f (ContinuousLinearMap.rotation t p).1)
      (df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) θ :=
    fun θ => (hf _).comp_hasDerivAt θ (hasDerivAt_rotation_fst θ p)
  have hc : Continuous (fun θ =>
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hc.intervalIntegrable 0 (π / 2))
  simpa [ContinuousLinearMap.rotation_apply] using hi

theorem rotation_exp_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df) (r : ℝ) (p : E × E) :
    exp (r * (f p.2 - f p.1)) ≤ (π / 2)⁻¹ *
      ∫ θ in (0 : ℝ)..π / 2, exp (r * (π / 2) *
        df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
  have hc : Continuous (fun θ => r * (π / 2) *
      df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) := by
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have hJ := exp_interval_average_le (half_pos pi_pos) hc
  rw [intervalIntegral.integral_const_mul, rotation_fundamental_theorem hf hdf] at hJ
  convert hJ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  field_simp

theorem exp_dual_le {L : ℝ≥0} (D : StrongDual ℝ E) (hD : ‖D‖ ≤ L) (r : ℝ) (y : E) :
    exp (r * D y) ≤ exp (|r| * L * ‖y‖) := by
  apply exp_le_exp.mpr
  calc
    r * D y ≤ |r * D y| := le_abs_self _
    _ = |r| * ‖D y‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |r| * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (abs_nonneg _)
    _ ≤ |r| * ((L : ℝ) * ‖y‖) := by gcongr
    _ = _ := by ring

theorem rotation_exp_dual_le {L : ℝ≥0} {df : E → StrongDual ℝ E}
    (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) (p : E × E) :
    exp (r * df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2) ≤
      exp (|r| * L * ‖p.1‖) * exp (|r| * L * ‖p.2‖) := by
  calc
    _ ≤ exp (|r| * L * ‖(ContinuousLinearMap.rotation θ p).2‖) := exp_dual_le _ (hdf _) _ _
    _ ≤ exp (|r| * L * (‖p.1‖ + ‖p.2‖)) := by
      gcongr
      exact rotation_snd_norm_le θ p
    _ = _ := by rw [mul_add, exp_add]

end Rotation

section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integrable_variable_dual {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * df p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
  apply ((gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)).comp_snd
    (stdGaussian E)).mono' (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_dual_le _ (hdf _) _ _

theorem stdGaussian_integral_variable_dual_le {df : E → StrongDual ℝ E} (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * df p.1 p.2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hi := stdGaussian_integrable_variable_dual hc hdf r
  have hio := hi.integral_prod_left
  simp only [stdGaussian_integral_exp_dual] at hio
  rw [integral_prod _ hi]
  simp only [stdGaussian_integral_exp_dual]
  calc
    _ ≤ ∫ _x : E, exp (r ^ 2 * (L : ℝ) ^ 2 / 2) ∂stdGaussian E := by
      apply integral_mono hio (integrable_const _)
      intro x
      apply exp_le_exp.mpr
      gcongr
      exact hdf x
    _ = _ := by simp

theorem stdGaussian_integral_rotation_variable_dual_le {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r θ : ℝ) :
    (∫ p : E × E, exp (r * df (ContinuousLinearMap.rotation θ p).1
        (ContinuousLinearMap.rotation θ p).2) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (r ^ 2 * (L : ℝ) ^ 2 / 2) := by
  have hm := IsGaussian.map_rotation_eq_self (μ := stdGaussian E) (by simp) θ
  rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
    (f := fun p : E × E => exp (r * df p.1 p.2)) (by fun_prop), hm]
  exact stdGaussian_integral_variable_dual_le hc hdf r

theorem stdGaussian_integrable_rotation_variable_dual {df : E → StrongDual ℝ E}
    (hc : Continuous df) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun z : ℝ × (E × E) =>
      exp (r * df (ContinuousLinearMap.rotation z.1 z.2).1
        (ContinuousLinearMap.rotation z.1 z.2).2))
      (ν.prod ((stdGaussian E).prod (stdGaussian E))) := by
  have hI := gaussian_integrable_exp_norm (μ := stdGaussian E) (|r| * L)
  apply ((hI.mul_prod hI).comp_snd ν).mono'
  · simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact rotation_exp_dual_le hdf _ _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lipschitz_of_bounded_derivative {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hf x).differentiableAt)
  intro x
  rw [(hf x).fderiv]
  exact hdf x

lemma exp_mul_sub (r a b : ℝ) : exp (r * (a - b)) = exp (-r * b) * exp (r * a) := by
  rw [← exp_add]
  congr 1
  ring

theorem stdGaussian_integrable_exp_difference {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun p : E × E => exp (r * (f p.2 - f p.1)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  simp_rw [exp_mul_sub]
  exact (gaussian_integrable_exp_lipschitz hf (-r)).mul_prod
    (gaussian_integrable_exp_lipschitz hf r)

theorem stdGaussian_mgf_difference_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ p : E × E, exp (r * (f p.2 - f p.1)) ∂(stdGaussian E).prod (stdGaussian E)) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (π / 2))
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let R := r * (π / 2)
  let G : ℝ → E × E → ℝ := fun θ p => exp (R *
    df (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2)
  have hI : Integrable (Function.uncurry G) (ν.prod ((stdGaussian E).prod (stdGaussian E))) :=
    stdGaussian_integrable_rotation_variable_dual hc hdf R ν
  have hD := stdGaussian_integrable_exp_difference (lipschitz_of_bounded_derivative hf hdf) r
  have hpos : 0 < π / 2 := half_pos pi_pos
  have hvol : ν.real univ = π / 2 := by
    simp [ν, measureReal_def, Real.volume_Ioc, hpos.le]
  have hpoint (p : E × E) : exp (r * (f p.2 - f p.1)) ≤
      (π / 2)⁻¹ * ∫ θ, G θ p ∂ν := by
    simpa only [intervalIntegral.integral_of_le hpos.le] using rotation_exp_difference_le hf hc r p
  calc
    _ ≤ ∫ p : E × E, (π / 2)⁻¹ * (∫ θ, G θ p ∂ν)
        ∂(stdGaussian E).prod (stdGaussian E) :=
      integral_mono hD (hI.integral_prod_right.const_mul _) hpoint
    _ = (π / 2)⁻¹ * ∫ θ, (∫ p : E × E, G θ p
        ∂(stdGaussian E).prod (stdGaussian E)) ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hI]
    _ ≤ (π / 2)⁻¹ * ∫ _θ, exp (R ^ 2 * (L : ℝ) ^ 2 / 2) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      apply integral_mono hI.integral_prod_left (integrable_const _)
      intro θ
      exact stdGaussian_integral_rotation_variable_dual_le hc hdf R θ
    _ = exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      rw [integral_const, smul_eq_mul, hvol, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      congr 1
      dsimp [R]
      ring

theorem stdGaussian_mgf_centered_le {f : E → ℝ} {df : E → StrongDual ℝ E}
    (hf : ∀ x, HasFDerivAt f (df x) x) (hc : Continuous df)
    {L : ℝ≥0} (hdf : ∀ x, ‖df x‖ ≤ L) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hLip := lipschitz_of_bounded_derivative hf hdf
  have hF := gaussian_integrable_lipschitz (μ := stdGaussian E) hLip
  have hG := gaussian_integrable_exp_lipschitz (μ := stdGaussian E) hLip (-r)
  have hpair := stdGaussian_integrable_exp_difference hLip (-r)
  have hcenter : Integrable (fun x => exp (r * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hLip r).const_mul _
  have hj (x : E) : exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ≤
      ∫ y, exp (r * (f x - f y)) ∂stdGaussian E := by
    have hsub := ((integrable_const (f x)).sub hF).const_mul r
    have he : Integrable (fun y => exp (r * (f x - f y))) (stdGaussian E) := by
      simp_rw [exp_mul_sub]
      exact hG.mul_const _
    have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (by filter_upwards [] with y; exact mem_univ _) hsub he
    simp only [Pi.sub_apply] at h
    simpa only [integral_const_mul, integral_sub (integrable_const _) hF,
      integral_const, probReal_univ, one_smul] using h
  have heq (x y : E) : r * (f x - f y) = -r * (f y - f x) := by ring
  simp_rw [heq] at hj
  calc
    _ ≤ ∫ x, (∫ y, exp (-r * (f y - f x)) ∂stdGaussian E) ∂stdGaussian E :=
      integral_mono hcenter hpair.integral_prod_left hj
    _ = ∫ p : E × E, exp (-r * (f p.2 - f p.1))
        ∂(stdGaussian E).prod (stdGaussian E) := (integral_prod _ hpair).symm
    _ ≤ exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
      simpa using stdGaussian_mgf_difference_le hf hc hdf (-r)

theorem centered_mgf_le_of_uniform_dist {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {δ : ℝ}
    (hfg : ∀ x, dist (f x) (g x) ≤ δ) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (2 * |r| * δ) *
        (∫ x, exp (r * (g x - ∫ y, g y ∂stdGaussian E)) ∂stdGaussian E) := by
  let μ := stdGaussian E
  have hfi : Integrable f μ := gaussian_integrable_lipschitz hf
  have hgi : Integrable g μ := gaussian_integrable_lipschitz hg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ δ := by
    have hi : ‖∫ x, f x - g x ∂μ‖ ≤ δ * μ.real univ :=
      norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall (fun x => by simpa only [dist_eq_norm] using hfg x))
    rw [integral_sub hfi hgi] at hi
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi
  have he (h : E → ℝ) {K : ℝ≥0} (hh : LipschitzWith K h) :
      Integrable (fun x => exp (r * (h x - ∫ y, h y ∂μ))) μ := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hh r).const_mul _
  rw [← integral_const_mul]
  apply integral_mono (he f hf) ((he g hg).const_mul _)
  intro x
  dsimp only
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hdiff : |(f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)| ≤ 2 * δ := by
    have hx : |f x - g x| ≤ δ := by simpa only [Real.dist_eq] using hfg x
    calc
      _ = |(f x - g x) - ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)| := by congr 1; ring
      _ ≤ |f x - g x| + |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (f x - g x) ((∫ y, f y ∂μ) - ∫ y, g y ∂μ)
      _ ≤ 2 * δ := by linarith
  have hh := le_abs_self (r * ((f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)))
  rw [abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hdiff (abs_nonneg r)
  dsimp [μ] at *
  nlinarith

end StandardGaussianRotation
end SKGap
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StdGaussianMgfLipschitz
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
namespace SKGap
section StandardGaussianRotation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_mgf_lipschitz_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (r : ℝ) :
    (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      (∫ x, exp (r * (f x - ∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤
        exp (2 * |r| * ((L : ℝ) * ε)) * exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8) := by
    obtain ⟨g, hgs, hgl, hgf⟩ := exists_smooth_lipschitz_approx hf hε
    have hmg := stdGaussian_mgf_centered_le
      (fun x => (hgs.differentiable (by simp) x).hasFDerivAt)
      (hgs.continuous_fderiv (by simp)) (fun _ => norm_fderiv_le_of_lipschitz ℝ hgl) r
    exact (centered_mgf_le_of_uniform_dist hf hgl
      (fun x => by simpa only [dist_comm] using hgf x) r).trans
        (mul_le_mul_of_nonneg_left hmg (exp_pos _).le)
  have ht : Tendsto (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) (𝓝[>] 0)
      (𝓝 (exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8))) := by
    have hc : Continuous (fun ε : ℝ => exp (2 * |r| * ((L : ℝ) * ε)) *
      exp (π ^ 2 * r ^ 2 * (L : ℝ) ^ 2 / 8)) := by fun_prop
    simpa using ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε heps
  exact hε ε heps

theorem stdGaussian_upper_tail_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {x | u ≤ f x - ∫ y, f y ∂stdGaussian E} ≤
      exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
  let t : ℝ := 4 * u / (π ^ 2 * (L : ℝ) ^ 2)
  have hLr : 0 < (L : ℝ) := hL
  have hden : 0 < π ^ 2 * (L : ℝ) ^ 2 := mul_pos (sq_pos_of_pos pi_pos) (sq_pos_of_pos hLr)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (by norm_num) hu) hden.le
  have hi : Integrable (fun x => exp (t * (f x - ∫ y, f y ∂stdGaussian E)))
      (stdGaussian E) := by
    simp_rw [exp_mul_sub]
    exact (gaussian_integrable_exp_lipschitz hf t).const_mul _
  calc
    _ ≤ exp (-t * u) * ∫ x, exp (t * (f x - ∫ y, f y ∂stdGaussian E))
        ∂stdGaussian E := measure_ge_le_exp_mul_mgf u ht hi
    _ ≤ exp (-t * u) * exp (π ^ 2 * t ^ 2 * (L : ℝ) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (stdGaussian_mgf_lipschitz_le hf t) (exp_pos _).le
    _ = exp (-2 * u ^ 2 / (π ^ 2 * (L : ℝ) ^ 2)) := by
      rw [← exp_add]
      congr 1
      dsimp [t]
      field_simp
      ring

end StandardGaussianRotation
end SKGap

end
end
end
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

lemma opNorm_sub (M N : Matrix ι ι ℝ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (M-N)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

lemma real_sandwich_opNorm (D V : Matrix ι ι ℝ) :
    opNorm (D*V*D) ≤ opNorm D^2*opNorm V := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (D*V*D)‖ ≤
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D‖^2*‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V‖
  simp only [map_mul]
  have h := (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D*Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V))
      (norm_nonneg _))
  exact h.trans_eq (by ring)

lemma real_sandwich_stability_norm (D C M : Matrix ι ι ℝ) :
    opNorm (1-D*(M-C)*D) ≤ 1+opNorm D^2*(opNorm M+opNorm C) := by
  calc
    _ ≤ opNorm (1 : Matrix ι ι ℝ)+opNorm (D*(M-C)*D) := opNorm_sub _ _
    _ ≤ 1+opNorm D^2*(opNorm M+opNorm C) :=
      add_le_add opNorm_one_le ((real_sandwich_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_sub _ _) (sq_nonneg _)))

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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductUpperTailLipschitz
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
namespace SKGap
section ProductGaussianConcentration
variable {κ : Type*} [Fintype κ]

theorem gaussianProduct_upper_tail_lipschitz {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} ≤
      Real.exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hp : MeasurePreserving e (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨e.measurable, map_pi_eq_stdGaussian⟩
  have hi := hp.integral_comp' (fun x : EuclideanSpace ℝ κ => f x.ofLp)
  change (∫ x, f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hi
  have h := stdGaussian_upper_tail_lipschitz hf hL hu
  rw [← hi] at h
  have hs : MeasurableSet {x : EuclideanSpace ℝ κ |
      u ≤ f x.ofLp - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} :=
    measurableSet_le measurable_const (hf.continuous.measurable.sub_const _)
  have he := hp.measure_preimage hs.nullMeasurableSet
  have her := congrArg ENNReal.toReal he
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)} = _ at her
  rw [her]
  exact h

end ProductGaussianConcentration
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianQuadratic
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
namespace SKGap
open scoped BigOperators

lemma gaussian_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma gaussian_memLp_sq : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_integrable_pow 4

lemma gaussian_integral_sq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one] using h

lemma gaussian_integral_fourth : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
    convert! (hasDerivAt_id x).pow 3 using 1; norm_num [Pi.pow_apply, id_eq]
  have hi : Integrable (fun x : ℝ => (x - 0)*x^3) (gaussianReal 0 1) := by
    simpa only [sub_zero, ← pow_succ'] using gaussian_integrable_pow 4
  have h := gaussian_integration_by_parts (by norm_num : (1 : ℝ≥0) ≠ 0)
    hd (gaussian_integrable_pow 3) ((gaussian_integrable_pow 2).const_mul 3) hi
  simpa only [sub_zero, ← pow_succ', integral_const_mul, gaussian_integral_sq,
    NNReal.coe_one, one_mul, mul_one] using h

lemma gaussian_variance_sq : Var[fun x : ℝ => x^2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub gaussian_memLp_sq]
  simp only [Pi.pow_apply, ← pow_mul, gaussian_integral_fourth, gaussian_integral_sq]
  norm_num

section Quadratic
variable {ι : Type*} [Fintype ι]

lemma gaussianQuadratic_memLp (a : ι → ℝ) :
    MemLp (gaussianQuadratic a) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply memLp_finsetSum
  intro i _
  exact ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i))

lemma gaussianQuadratic_mean (a : ι → ℝ) :
    (∫ x, gaussianQuadratic a x ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianQuadratic
  have hi (i : ι) : Integrable (fun x : ι → ℝ => a i * (x i)^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  have he : (∫ x : ι → ℝ, (x i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ y : ℝ, y^2 ∂gaussianReal 0 1 :=
    integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      (f := fun y : ℝ => y^2) (by fun_prop)
  rw [he, gaussian_integral_sq, mul_one]

lemma gaussianQuadratic_variance (a : ι → ℝ) :
    Var[gaussianQuadratic a; Measure.pi (fun _ : ι => gaussianReal 0 1)] =
      2 * ∑ i, (a i)^2 := by
  have h : Var[gaussianQuadratic a; Measure.pi (fun _ : ι => gaussianReal 0 1)] =
      ∑ i, Var[fun x : ℝ => a i * x^2; gaussianReal 0 1] := by
    convert variance_sum_pi (fun i : ι => gaussian_memLp_sq.const_mul (a i)) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    simp only [gaussianQuadratic, Finset.sum_apply]
  rw [h]
  simp only [variance_const_mul, gaussian_variance_sq, ← Finset.sum_mul]
  ring

end Quadratic

lemma sqrt_sub_sq_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (sqrt x - sqrt y)^2 ≤ |x-y| := by
  have hx2 := sq_sqrt hx
  have hy2 := sq_sqrt hy
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := sqrt_le_sqrt h
    nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hh)]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := sqrt_le_sqrt h
    nlinarith [mul_nonneg (sqrt_nonneg y) (sub_nonneg.mpr hh)]

section Fluctuation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma memLp_sqrt_of_nonneg {f : Ω → ℝ} (hf : Integrable f μ)
    (hpos : ∀ x, 0 ≤ f x) : MemLp (fun x => sqrt (f x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  exact hf.congr (Filter.Eventually.of_forall (fun x => (sq_sqrt (hpos x)).symm))

lemma integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ sqrt (∫ x, (f x)^2 ∂μ) := by
  have h0 := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at h0
  have hsq : (∫ x, |f x| ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
    simpa only [Real.norm_eq_abs, Pi.pow_apply, sq_abs, sub_nonneg] using h0
  have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hh := sq_sqrt hi
  have hp := sqrt_nonneg (∫ x, (f x)^2 ∂μ)
  nlinarith [sq_nonneg ((∫ x, |f x| ∂μ) - sqrt (∫ x, (f x)^2 ∂μ))]

theorem integral_sqrt_fluctuation {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (hpos : ∀ x, 0 ≤ f x) :
    (∫ x, |sqrt (f x) - sqrt (∫ y, f y ∂μ)| ∂μ) ≤ sqrt (sqrt (Var[f; μ])) := by
  let m := ∫ y, f y ∂μ
  have hm : 0 ≤ m := integral_nonneg hpos
  have hg : MemLp (fun x => f x - m) 2 μ := hf.sub (memLp_const m)
  have hroot : MemLp (fun x => sqrt (f x) - sqrt m) 2 μ := by
    apply (memLp_two_iff_integrable_sq ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const)).mpr
    apply hg.integrable (by norm_num) |>.norm |>.mono'
      (((Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const).pow 2)
    filter_upwards [] with x
    change |(sqrt (f x) - sqrt m)^2| ≤ |f x - m|
    rw [abs_of_nonneg (sq_nonneg (sqrt (f x) - sqrt m))]
    exact sqrt_sub_sq_le_abs_sub (hpos x) hm
  have hdiff : (∫ x, (sqrt (f x) - sqrt m)^2 ∂μ) ≤ ∫ x, |f x-m| ∂μ := by
    apply integral_mono hroot.integrable_sq (hg.integrable (by norm_num)).norm
    exact fun x => sqrt_sub_sq_le_abs_sub (hpos x) hm
  have hc := integral_abs_le_sqrt_sq hg
  rw [← variance_eq_integral hf.aemeasurable] at hc
  exact (integral_abs_le_sqrt_sq hroot).trans (sqrt_le_sqrt (hdiff.trans hc))

end Fluctuation
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpSum
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
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem expSum_pos (κ : ℝ) (x : ι → ℝ) : 0 < expSum κ x := by
  exact Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty

theorem softWeight_pos (κ : ℝ) (x : ι → ℝ) (i : ι) : 0 < softWeight κ x i :=
  div_pos (exp_pos _) (expSum_pos κ x)

theorem sum_softWeight (κ : ℝ) (x : ι → ℝ) : ∑ i, softWeight κ x i = 1 := by
  simp only [softWeight, ← Finset.sum_div]
  exact div_self (expSum_pos κ x).ne'

theorem softWeight_le_one (κ : ℝ) (x : ι → ℝ) (i : ι) : softWeight κ x i ≤ 1 := by
  rw [← sum_softWeight κ x]
  exact Finset.single_le_sum (fun j _ => (softWeight_pos κ x j).le) (Finset.mem_univ i)

theorem continuous_softWeight (κ : ℝ) (i : ι) : Continuous (fun x : ι → ℝ => softWeight κ x i) := by
  apply Continuous.div
  · exact continuous_exp.comp (continuous_const.mul (continuous_apply i))
  · exact continuous_finsetSum _ (fun j _ => continuous_exp.comp (continuous_const.mul (continuous_apply j)))
  · exact fun x => (expSum_pos κ x).ne'

theorem continuous_smoothMax (κ : ℝ) : Continuous (smoothMax κ : (ι → ℝ) → ℝ) := by
  apply Continuous.div_const
  exact (continuous_finsetSum _ (fun j _ => continuous_exp.comp (continuous_const.mul (continuous_apply j)))).log
    (fun x => (expSum_pos κ x).ne')

omit [Nonempty ι] in
theorem hasDerivAt_expSum {κ t : ℝ} {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) :
    HasDerivAt (fun s => expSum κ (fun i => f i s))
      (∑ i, Real.exp (κ * f i t) * (κ * df i)) t := by
  convert! HasDerivAt.fun_sum (fun i _ => ((hf i).const_mul κ).exp) using 1
  all_goals try with_reducible_and_instances rfl

theorem hasDerivAt_smoothMax {κ t : ℝ} (hκ : κ ≠ 0) {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) :
    HasDerivAt (fun s => smoothMax κ (fun i => f i s))
      (∑ i, softWeight κ (fun j => f j t) i * df i) t := by
  convert! ((hasDerivAt_expSum hf).log (expSum_pos κ (fun j => f j t)).ne').div_const κ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [softWeight]
  have hs : (∑ i, Real.exp (κ * f i t) * (κ * df i)) =
      κ * ∑ i, Real.exp (κ * f i t) * df i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [hκ, (expSum_pos κ (fun j => f j t)).ne']

theorem hasDerivAt_softWeight {κ t : ℝ} {f : ι → ℝ → ℝ} {df : ι → ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i) t) (i : ι) :
    HasDerivAt (fun s => softWeight κ (fun j => f j s) i)
      (κ * softWeight κ (fun j => f j t) i *
        (df i - ∑ j, softWeight κ (fun k => f k t) j * df j)) t := by
  convert! (((hf i).const_mul κ).exp).div (hasDerivAt_expSum hf)
    (expSum_pos κ (fun j => f j t)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [softWeight]
  have hs : (∑ j, Real.exp (κ * f j t) * (κ * df j)) =
      κ * ∑ j, Real.exp (κ * f j t) * df j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(expSum_pos κ (fun j => f j t)).ne']

theorem weighted_abs_le (κ : ℝ) (x v : ι → ℝ) :
    |∑ i, softWeight κ x i * v i| ≤ ∑ i, |v i| := by
  calc
    _ ≤ ∑ i, |softWeight κ x i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (softWeight_pos κ x i)]
      exact mul_le_of_le_one_left (abs_nonneg _) (softWeight_le_one κ x i)

omit [Nonempty ι] in
theorem smoothMax_ge {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) (i : ι) :
    x i ≤ smoothMax κ x := by
  rw [smoothMax, le_div_iff₀ hκ]
  calc
    x i * κ = log (Real.exp (κ * x i)) := by rw [log_exp]; ring
    _ ≤ log (expSum κ x) := log_le_log (exp_pos _) <|
      Finset.single_le_sum (fun j _ => (exp_pos (κ * x j)).le) (Finset.mem_univ i)

theorem smoothMax_le {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) {b : ℝ}
    (hb : ∀ i, x i ≤ b) : smoothMax κ x ≤ b + log (Fintype.card ι) / κ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [smoothMax, div_le_iff₀ hκ]
  calc
    log (expSum κ x) ≤ log ((Fintype.card ι : ℝ) * Real.exp (κ * b)) := by
      apply log_le_log (expSum_pos _ _)
      calc
        _ ≤ ∑ _ : ι, Real.exp (κ * b) := Finset.sum_le_sum (fun i _ => exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb i) hκ.le))
        _ = _ := by simp
    _ = _ := by rw [log_mul hn.ne' (exp_pos _).ne', log_exp]; field_simp; ring

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem continuous_affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Continuous (affineProcess m a) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_apply k)))

omit [Fintype ι] [Nonempty ι] in
theorem affineProcess_coordinate_hasDerivAt {n : ℕ} (m : ι → ℝ)
    (a : ι → Fin (n + 1) → ℝ) (i : ι) (k : Fin (n + 1)) (u : Fin n → ℝ) (z : ℝ) :
    HasDerivAt (fun z => affineProcess m a (k.insertNth z u) i) (a i k) z := by
  have he (z : ℝ) : affineProcess m a (k.insertNth z u) i =
      a i k * z + (m i + ∑ l, a i (k.succAbove l) * u l) := by
    rw [affineProcess, Fin.sum_univ_succAbove _ k]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring
  simp_rw [he]
  convert! ((hasDerivAt_id z).const_mul (a i k)).add_const (m i + ∑ l, a i (k.succAbove l) * u l) using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem affine_softWeight_coordinate_IBP {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin (n + 1) → ℝ) (i : ι) (k : Fin (n + 1)) :
    (∫ z, z k * softWeight κ (affineProcess m a z) i ∂standardGaussianProduct (n + 1)) =
      ∫ z, κ * softWeight κ (affineProcess m a z) i *
        (a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k)
        ∂standardGaussianProduct (n + 1) := by
  apply gaussianProduct_coordinate_IBP (C := 1) (D := |κ| * (|a i k| + ∑ j, |a j k|)) k
  · exact (continuous_softWeight κ i).comp (continuous_affineProcess m a)
  · exact (continuous_const.mul ((continuous_softWeight κ i).comp (continuous_affineProcess m a))).mul
      (continuous_const.sub (continuous_finsetSum _ (fun j _ =>
        ((continuous_softWeight κ j).comp (continuous_affineProcess m a)).mul continuous_const)))
  · intro z
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _
  · intro z
    rw [norm_mul, norm_mul, Real.norm_eq_abs κ,
      Real.norm_eq_abs (softWeight _ _ _), abs_of_pos (softWeight_pos _ _ _), Real.norm_eq_abs]
    apply mul_le_mul
    · exact mul_le_of_le_one_right (abs_nonneg κ) (softWeight_le_one _ _ _)
    · exact (abs_sub _ _).trans (add_le_add_right (weighted_abs_le κ _ (fun j => a j k)) _)
    · positivity
    · positivity
  · intro u z
    exact hasDerivAt_softWeight (fun j => affineProcess_coordinate_hasDerivAt m a j k u z) i

omit [Nonempty ι] in
theorem weighted_covariance_identity (p u v : ι → ℝ) (hp : ∑ i, p i = 1) :
    (∑ i, p i * u i * v i) - (∑ i, p i * u i) * (∑ i, p i * v i) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * (u i - u j) * (v i - v j) := by
  have he (i j : ι) : p i * p j * (u i - u j) * (v i - v j) =
      (p i * u i * v i) * p j + p i * (p j * u j * v j) -
        (p i * u i) * (p j * v j) - (p i * v i) * (p j * u j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hp]
  ring

theorem smoothMax_norm_le {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) :
    ‖smoothMax κ x‖ ≤ ∑ i, |x i| + log (Fintype.card ι) / κ := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ log (Fintype.card ι) / κ := div_nonneg (log_nonneg hn) hκ.le
  have hb (i : ι) : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · let i : ι := Classical.choice inferInstance
    have hlo := smoothMax_ge hκ x i
    have ha := (abs_le.mp (hb i)).1
    linarith
  · exact smoothMax_le hκ x (fun i => (le_abs_self _).trans (hb i))

omit [Fintype ι] [Nonempty ι] in
theorem interpolatedCoeff_abs_le {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) :
    |interpolatedCoeff a b t i k| ≤ |a i k| + |b i k| := by
  calc
    _ ≤ |sin t * a i k| + |cos t * b i k| := abs_add_le _ _
    _ ≤ 1 * |a i k| + 1 * |b i k| := by
      simp only [abs_mul]
      gcongr
      · exact abs_sin_le_one t
      · exact abs_cos_le_one t
    _ = _ := by ring

omit [Fintype ι] [Nonempty ι] in
theorem interpolatedCoeffDeriv_abs_le {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) :
    |interpolatedCoeffDeriv a b t i k| ≤ |a i k| + |b i k| := by
  calc
    _ ≤ |cos t * a i k| + |sin t * b i k| := abs_sub _ _
    _ ≤ 1 * |a i k| + 1 * |b i k| := by
      simp only [abs_mul]
      gcongr
      · exact abs_cos_le_one t
      · exact abs_sin_le_one t
    _ = _ := by ring

omit [Nonempty ι] in
theorem integrable_processBound {n : ℕ} (a b : ι → Fin n → ℝ) :
    Integrable (processBound a b) (standardGaussianProduct n) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  exact ((integrable_eval (i := k) IsGaussian.integrable_id).norm).const_mul _

omit [Fintype ι] [Nonempty ι] in
theorem interpolated_affine_hasDerivAt {n : ℕ} (m : ι → ℝ) (a b : ι → Fin n → ℝ)
    (z : Fin n → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun t => affineProcess m (interpolatedCoeff a b t) z i)
      (∑ k, interpolatedCoeffDeriv a b t i k * z k) t := by
  convert! (HasDerivAt.fun_sum (fun k _ =>
    (((Real.hasDerivAt_sin t).mul_const (a i k)).add
      ((Real.hasDerivAt_cos t).mul_const (b i k))).mul_const (z k))).const_add (m i) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro k _
  dsimp [interpolatedCoeffDeriv]
  ring

theorem interpolationDerivative_norm_le {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a b : ι → Fin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    ‖interpolationDerivative κ m a b t z‖ ≤ processBound a b z := by
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ i, |∑ k, interpolatedCoeffDeriv a b t i k * z k| := weighted_abs_le _ _ _
    _ ≤ ∑ i, ∑ k, (|a i k| + |b i k|) * |z k| := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (interpolatedCoeffDeriv_abs_le a b t i k) (abs_nonneg _)

theorem interpolated_smoothMax_norm_le {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (m : ι → ℝ)
    (a b : ι → Fin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    ‖smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)‖ ≤
      (∑ i, |m i|) + processBound a b z + log (Fintype.card ι) / κ := by
  apply (smoothMax_norm_le hκ _).trans
  gcongr
  rw [processBound, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply (abs_add_le _ _).trans
  gcongr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (interpolatedCoeff_abs_le a b t i k) (abs_nonneg _)

theorem interpolation_hasDerivAt {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (m : ι → ℝ) (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∫ z, smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)
      ∂standardGaussianProduct n)
      (∫ z, interpolationDerivative κ m a b t z ∂standardGaussianProduct n) t := by
  have hp (t : ℝ) (i : ι) :
      Continuous (fun z => softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i) :=
    (continuous_softWeight κ i).comp (continuous_affineProcess m _)
  have hf (t : ℝ) : Continuous (fun z => smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)) :=
    (continuous_smoothMax κ).comp (continuous_affineProcess m _)
  have hdf (t : ℝ) : Continuous (interpolationDerivative κ m a b t) := by
    apply continuous_finsetSum
    intro i _
    exact (hp t i).mul (continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_apply k)))
  have hb : Integrable (fun z => (∑ i, |m i|) + processBound a b z + log (Fintype.card ι) / κ)
      (standardGaussianProduct n) :=
    ((integrable_const _).add (integrable_processBound a b)).add (integrable_const _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardGaussianProduct n) (s := univ) (x₀ := t)
    (F := fun t z => smoothMax κ (affineProcess m (interpolatedCoeff a b t) z))
    (F' := fun t z => interpolationDerivative κ m a b t z)
    (bound := processBound a b)
    Filter.univ_mem (Filter.Eventually.of_forall (fun t => (hf t).aestronglyMeasurable))
    (hb.mono' (hf t).aestronglyMeasurable (ae_of_all _ (interpolated_smoothMax_norm_le hκ m a b t)))
    (hdf t).aestronglyMeasurable
    (ae_of_all _ (fun z t _ => interpolationDerivative_norm_le κ m a b t z))
    (integrable_processBound a b)
    (ae_of_all _ (fun z t _ => hasDerivAt_smoothMax hκ.ne'
      (fun i => interpolated_affine_hasDerivAt m a b z t i)))).2

theorem integrable_affine_weight {n : ℕ} (κ : ℝ) (m : ι → ℝ) (a : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun z => softWeight κ (affineProcess m a z) i) (standardGaussianProduct n) := by
  apply Integrable.of_bound ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable 1
  exact ae_of_all _ (fun z => by
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _)

theorem integrable_coordinate_weight {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    Integrable (fun z => z k * softWeight κ (affineProcess m a z) i) (standardGaussianProduct n) := by
  apply Integrable.mul_bdd (integrable_eval (i := k) IsGaussian.integrable_id)
    ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos _ _ _)]
    exact softWeight_le_one _ _ _)

theorem integrable_weight_covariance {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    Integrable (fun z => κ * softWeight κ (affineProcess m a z) i *
      (a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k))
      (standardGaussianProduct n) := by
  have hi : Integrable (fun z => a i k - ∑ j, softWeight κ (affineProcess m a z) j * a j k)
      (standardGaussianProduct n) := by
    apply (integrable_const _).sub
    exact integrable_finsetSum _ (fun j _ => (integrable_affine_weight κ m a j).mul_const _)
  have hm := hi.bdd_mul ((continuous_softWeight κ i).comp (continuous_affineProcess m a)).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      simp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_pos (softWeight_pos κ (affineProcess m a z) i)]
      exact softWeight_le_one _ _ _))
  convert! hm.const_mul κ using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [Function.comp_def]
  ring

omit [Nonempty ι] in
theorem weighted_matrix_covariance_identity {n : ℕ} (p : ι → ℝ) (a d : ι → Fin n → ℝ)
    (hp : ∑ i, p i = 1) :
    (∑ i, ∑ k, d i k * p i * (a i k - ∑ j, p j * a j k)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * ∑ k, (d i k - d j k) * (a i k - a j k) := by
  have hk (k : Fin n) :
      (∑ i, d i k * p i * (a i k - ∑ j, p j * a j k)) =
        (1/2:ℝ) * ∑ i, ∑ j, p i * p j * (d i k - d j k) * (a i k - a j k) := by
    rw [← weighted_covariance_identity p (fun i => d i k) (fun i => a i k) hp]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [Finset.sum_comm]
  simp_rw [hk, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gaussian_linear_weight_IBP {n : ℕ} (κ : ℝ) (m : ι → ℝ)
    (a d : ι → Fin (n + 1) → ℝ) :
    (∫ z, ∑ i, softWeight κ (affineProcess m a z) i * ∑ k, d i k * z k
      ∂standardGaussianProduct (n + 1)) =
      (κ / 2) * ∫ z, ∑ i, ∑ j,
        softWeight κ (affineProcess m a z) i * softWeight κ (affineProcess m a z) j *
        ∑ k, (d i k - d j k) * (a i k - a j k)
        ∂standardGaussianProduct (n + 1) := by
  let p := fun z i => softWeight κ (affineProcess m a z) i
  have hi (i : ι) (k : Fin (n + 1)) : Integrable (fun z => d i k * (z k * p z i))
      (standardGaussianProduct (n + 1)) := (integrable_coordinate_weight κ m a i k).const_mul _
  have hr (i : ι) (k : Fin (n + 1)) : Integrable (fun z => d i k *
      (κ * p z i * (a i k - ∑ j, p z j * a j k))) (standardGaussianProduct (n + 1)) :=
    (integrable_weight_covariance κ m a i k).const_mul _
  calc
    _ = ∫ z, ∑ i, ∑ k, d i k * (z k * p z i) ∂standardGaussianProduct (n + 1) := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [p]
      ring
    _ = ∑ i, ∑ k, d i k * ∫ z, z k * p z i ∂standardGaussianProduct (n + 1) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hi i k)]
      simp only [integral_const_mul]
    _ = ∑ i, ∑ k, d i k * ∫ z, κ * p z i * (a i k - ∑ j, p z j * a j k)
        ∂standardGaussianProduct (n + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [affine_softWeight_coordinate_IBP]
    _ = ∫ z, ∑ i, ∑ k, d i k * (κ * p z i * (a i k - ∑ j, p z j * a j k))
        ∂standardGaussianProduct (n + 1) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hr i k))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun k _ => hr i k)]
      simp only [integral_const_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      have he := weighted_matrix_covariance_identity (p z) a d (sum_softWeight κ _)
      calc
        _ = κ * ∑ i, ∑ k, d i k * p z i * (a i k - ∑ j, p z j * a j k) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [he]; dsimp [p]; ring

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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteMax
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
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
omit [Fintype ι] [Nonempty ι] in
theorem interpolation_increment_identity {n : ℕ} (a b : ι → Fin n → ℝ) (i j : ι) (t : ℝ)
    (horth : ∑ k, (a i k - a j k) * (b i k - b j k) = 0) :
    (∑ k, (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
      (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k)) =
      sin t * cos t * ((∑ k, (a i k - a j k) ^ 2) - ∑ k, (b i k - b j k) ^ 2) := by
  have he (k : Fin n) :
      (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
        (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k) =
      sin t * cos t * (a i k - a j k)^2 - sin t * cos t * (b i k - b j k)^2 +
        (cos t ^ 2 - sin t ^ 2) * ((a i k - a j k) * (b i k - b j k)) := by
    dsimp [interpolatedCoeff, interpolatedCoeffDeriv]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [horth]
  ring

theorem interpolation_derivative_nonneg {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2)
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    0 ≤ ∫ z, interpolationDerivative κ m a b t z ∂standardGaussianProduct (n + 1) := by
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos, ht.2])
  have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, ht.1], ht.2⟩
  rw [show (fun z => interpolationDerivative κ m a b t z) =
      (fun z => ∑ i, softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i *
        ∑ k, interpolatedCoeffDeriv a b t i k * z k) from rfl,
    gaussian_linear_weight_IBP]
  apply mul_nonneg (div_nonneg hκ (by norm_num))
  apply integral_nonneg
  intro z
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (softWeight_pos _ _ _).le (softWeight_pos _ _ _).le)
  rw [interpolation_increment_identity a b i j t (horth i j)]
  exact mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hinc i j))

theorem gaussian_smoothMax_comparison {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  let f := fun t => ∫ z, smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)
    ∂standardGaussianProduct (n + 1)
  have hmono : MonotoneOn f (Icc 0 (π / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (interpolation_hasDerivAt hκ m a b t).continuousAt)).continuousOn
      (fun t _ => (interpolation_hasDerivAt hκ m a b t).hasDerivWithinAt)
    intro t ht
    exact interpolation_derivative_nonneg hκ.le m a b horth hinc (interior_subset ht)
  have hle := hmono (show (0:ℝ) ∈ Icc 0 (π/2) from ⟨le_refl _, by positivity⟩)
    (show π/2 ∈ Icc (0:ℝ) (π/2) from ⟨by positivity, le_refl _⟩) (by positivity)
  have h0 : interpolatedCoeff a b 0 = b := by
    funext i k
    simp [interpolatedCoeff]
  have h1 : interpolatedCoeff a b (π/2) = a := by
    funext i k
    simp [interpolatedCoeff]
  simpa only [f, h0, h1] using hle

theorem le_finiteMax (x : ι → ℝ) (i : ι) : x i ≤ finiteMax x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem finiteMax_le {x : ι → ℝ} {b : ℝ} (hb : ∀ i, x i ≤ b) : finiteMax x ≤ b :=
  Finset.sup'_le _ _ (fun i _ => hb i)

theorem continuous_finiteMax : Continuous (finiteMax : (ι → ℝ) → ℝ) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem finiteMax_norm_le (x : ι → ℝ) : ‖finiteMax x‖ ≤ ∑ i, |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  change ‖Finset.univ.sup' Finset.univ_nonempty x‖ ≤ _
  rw [hi, Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

omit [Fintype ι] [Nonempty ι] in
theorem integrable_affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun z => affineProcess m a z i) (standardGaussianProduct n) := by
  apply (integrable_const _).add
  exact integrable_finsetSum _ (fun k _ => (integrable_eval (i := k) IsGaussian.integrable_id).const_mul _)

theorem integrable_finiteMax_affine {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => finiteMax (affineProcess m a z)) (standardGaussianProduct n) := by
  apply (integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).mono'
    (continuous_finiteMax.comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => finiteMax_norm_le _)

theorem integrable_smoothMax_affine {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => smoothMax κ (affineProcess m a z)) (standardGaussianProduct n) := by
  apply ((integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).add
    (integrable_const (log (Fintype.card ι) / κ))).mono'
    ((continuous_smoothMax κ).comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => smoothMax_norm_le hκ _)

theorem gaussian_finiteMax_comparison {n : ℕ}
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, finiteMax (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlog : 0 ≤ log (Fintype.card ι) := log_nonneg (by exact_mod_cast Fintype.card_pos)
  let κ := (log (Fintype.card ι) + 1) / ε
  have hκ : 0 < κ := div_pos (by linarith) hε
  have herr : log (Fintype.card ι) / κ ≤ ε := by
    apply (div_le_iff₀ hκ).mpr
    dsimp [κ]
    rw [mul_div_cancel₀ _ hε.ne']
    linarith
  calc
    _ ≤ ∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1) := by
      apply integral_mono (integrable_finiteMax_affine m b) (integrable_smoothMax_affine hκ m b)
      intro z
      exact finiteMax_le (fun i => smoothMax_ge hκ _ i)
    _ ≤ ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) :=
      gaussian_smoothMax_comparison hκ m a b horth hinc
    _ ≤ (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) + ε := by
      calc
        _ ≤ ∫ z, finiteMax (affineProcess m a z) + log (Fintype.card ι) / κ
            ∂standardGaussianProduct (n + 1) := by
          apply integral_mono (integrable_smoothMax_affine hκ m a)
            ((integrable_finiteMax_affine m a).add (integrable_const _))
          intro z
          exact smoothMax_le hκ _ (fun i => le_finiteMax _ i)
        _ = (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) +
            log (Fintype.card ι) / κ := by
          rw [integral_add (integrable_finiteMax_affine m a) (integrable_const _)]
          simp
        _ ≤ _ := add_le_add (le_refl _) herr

section CompactIndex
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

omit [CompactSpace I] [Nonempty I] in
theorem continuous_affine_index {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    Continuous (affineProcess m a z) := by
  exact hm.add (continuous_finsetSum _ (fun k _ => ((continuous_apply k).comp ha).mul continuous_const))

theorem supProcess_attained {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    ∃ i, supProcess m a z = affineProcess m a z i ∧
      ∀ j, affineProcess m a z j ≤ affineProcess m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_affine_index hm ha z).continuousOn
  exact ⟨i, by simpa [supProcess] using he, fun j => hi j (Set.mem_univ _)⟩

theorem affine_le_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) (i : I) :
    affineProcess m a z i ≤ supProcess m a z := by
  obtain ⟨j, he, hj⟩ := supProcess_attained hm ha z
  rw [he]
  exact hj i

theorem supProcess_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) {c : ℝ}
    (hc : ∀ i, affineProcess m a z i ≤ c) : supProcess m a z ≤ c := by
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
theorem continuous_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (supProcess m a) := by
  have hc : Continuous (fun p : (Fin n → ℝ) × I => affineProcess m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (affineProcess m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_abs_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    {M A : ℝ} (hm : ∀ i, |m i| ≤ M) (ha : ∀ i k, |a i k| ≤ A)
    (z : Fin n → ℝ) (i : I) :
    |affineProcess m a z i| ≤ M + A * ∑ k, |z k| := by
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| := add_le_add (hm i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem integrable_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (supProcess m a) (standardGaussianProduct n) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum _ (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_supProcess hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he, Real.norm_eq_abs]
  exact affineProcess_abs_le hMb hAb z i

theorem exists_finite_affine_net {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset I, t.Nonempty ∧ ∀ j, ∃ i ∈ t,
      |m j - m i| ≤ ε ∧ ∀ k, |a j k - a i k| ≤ ε := by
  let U : I → Set I := fun i => m ⁻¹' Metric.ball (m i) ε ∩ a ⁻¹' Metric.ball (a i) ε
  have ho (i : I) : IsOpen (U i) :=
    (Metric.isOpen_ball.preimage hm).inter (Metric.isOpen_ball.preimage ha)
  have hu : Set.univ ⊆ ⋃ i, U i := by
    intro j _
    apply Set.mem_iUnion.mpr
    exact ⟨j, by simp [U, hε]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U ho hu
  have hcover (j : I) : ∃ i ∈ t, j ∈ U i := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ j))
    obtain ⟨hit, hji⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hji⟩
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := hcover (Classical.choice inferInstance)
    exact ⟨i, hi⟩
  refine ⟨t, hne, fun j => ?_⟩
  obtain ⟨i, hi, hj⟩ := hcover j
  refine ⟨i, hi, ?_, fun k => ?_⟩
  · have hd : dist (m j) (m i) < ε := hj.1
    simpa only [Real.dist_eq] using hd.le
  · have hb : dist (a j) (a i) < ε := hj.2
    have hk := (dist_le_pi_dist (a j) (a i) k).trans_lt hb
    simpa only [Real.dist_eq] using hk.le

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_difference_abs_le {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ)
    {ε : ℝ} {i j : I} (hm : |m i - m j| ≤ ε)
    (ha : ∀ k, |a i k - a j k| ≤ ε) (z : Fin n → ℝ) :
    |affineProcess m a z i - affineProcess m a z j| ≤ ε * (1 + ∑ k, |z k|) := by
  have he : affineProcess m a z i - affineProcess m a z j =
      (m i - m j) + ∑ k, (a i k - a j k) * z k := by
    simp only [affineProcess, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ |m i - m j| + |∑ k, (a i k - a j k) * z k| := abs_add_le _ _
    _ ≤ ε + ∑ k, |(a i k - a j k) * z k| :=
      add_le_add hm (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε + ∑ k, ε * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha k) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem gaussian_supProcess_comparison {n : ℕ}
    {m : I → ℝ} {a b : I → Fin (n + 1) → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, supProcess m b z ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, supProcess m a z ∂standardGaussianProduct (n + 1) := by
  let μ := standardGaussianProduct (n + 1)
  let Z : (Fin (n + 1) → ℝ) → ℝ := fun z => 1 + ∑ k, |z k|
  have hZI : Integrable Z μ := (integrable_const 1).add
    (integrable_finsetSum _ (fun k _ => by
      have hi : Integrable (fun z : Fin (n + 1) → ℝ => z k) μ :=
        integrable_eval (i := k) IsGaussian.integrable_id
      simpa only [Real.norm_eq_abs] using hi.norm))
  have hZ : 0 ≤ ∫ z, Z z ∂μ := integral_nonneg (fun z => by dsimp [Z]; positivity)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / ((∫ z, Z z ∂μ) + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ * (∫ z, Z z ∂μ) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < (∫ z, Z z ∂μ) + 1)).mpr
    nlinarith
  obtain ⟨t, ht, hnet⟩ := exists_finite_affine_net hm hb hδ
  have : Nonempty t := ht.to_subtype
  let mf : t → ℝ := fun i => m i
  let af : t → Fin (n + 1) → ℝ := fun i => a i
  let bf : t → Fin (n + 1) → ℝ := fun i => b i
  have hfinite := gaussian_finiteMax_comparison mf af bf
    (fun i j => horth i j) (fun i j => hinc i j)
  calc
    _ ≤ ∫ z, finiteMax (affineProcess mf bf z) + δ * Z z ∂μ := by
      apply integral_mono (integrable_supProcess hm hb)
        ((integrable_finiteMax_affine mf bf).add (hZI.const_mul δ))
      intro z
      apply supProcess_le hm hb
      intro j
      obtain ⟨i, hi, hmj, hbj⟩ := hnet j
      have hd := (le_abs_self _).trans (affineProcess_difference_abs_le m b hmj hbj z)
      have hmax := le_finiteMax (affineProcess mf bf z) (⟨i, hi⟩ : t)
      change affineProcess m b z i ≤ _ at hmax
      change affineProcess m b z j ≤ finiteMax (affineProcess mf bf z) + δ * (1 + ∑ k, |z k|)
      linarith
    _ = (∫ z, finiteMax (affineProcess mf bf z) ∂μ) + δ * ∫ z, Z z ∂μ := by
      rw [integral_add (integrable_finiteMax_affine mf bf) (hZI.const_mul δ), integral_const_mul]
    _ ≤ (∫ z, finiteMax (affineProcess mf af z) ∂μ) + ε := add_le_add hfinite hδε
    _ ≤ (∫ z, supProcess m a z ∂μ) + ε := by
      refine add_le_add ?_ le_rfl
      apply integral_mono (integrable_finiteMax_affine mf af) (integrable_supProcess hm ha)
      intro z
      apply finiteMax_le
      intro i
      exact affine_le_supProcess hm ha z i

end CompactIndex
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianCoordinates
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
namespace SKGap
section ArbitraryCoordinates
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ]

omit [CompactSpace I] [Nonempty I] in
 theorem continuous_gaussianAffine {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    Continuous (gaussianAffine m a z) :=
  hm.add (continuous_finsetSum _ (fun k _ =>
    ((continuous_apply k).comp ha).mul continuous_const))

theorem gaussianSup_attained {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) :
    ∃ i, gaussianSup m a z = gaussianAffine m a z i ∧
      ∀ j, gaussianAffine m a z j ≤ gaussianAffine m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_gaussianAffine hm ha z).continuousOn
  exact ⟨i, by simpa [gaussianSup] using he, fun j => hi j (Set.mem_univ _)⟩

theorem gaussianSup_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : κ → ℝ) {c : ℝ}
    (hc : ∀ i, gaussianAffine m a z i ≤ c) : gaussianSup m a z ≤ c := by
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
 theorem continuous_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (gaussianSup m a) := by
  have hc : Continuous (fun p : (κ → ℝ) × I => gaussianAffine m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (gaussianAffine m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

theorem integrable_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (gaussianSup m a) (gaussianCoordinates κ) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by
    simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum (Finset.univ : Finset κ) (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_gaussianSup hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := gaussianSup_attained hm ha z
  rw [he, Real.norm_eq_abs]
  change |gaussianAffine m a z i| ≤ M + A * ∑ k, |z k|
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| :=
      add_le_add (hMb i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hAb i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem gaussianSup_comparison [Nonempty κ] {m : I → ℝ} {a b : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, gaussianSup m b z ∂gaussianCoordinates κ) ≤
      ∫ z, gaussianSup m a z ∂gaussianCoordinates κ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := κ))
  let e : Fin (n + 1) ≃ κ := (finCongr hn.symm).trans (Fintype.equivFin κ).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let a' : I → Fin (n + 1) → ℝ := fun i k => a i (e k)
  let b' : I → Fin (n + 1) → ℝ := fun i k => b i (e k)
  have ha' : Continuous a' := continuous_pi (fun k => (continuous_apply (e k)).comp ha)
  have hb' : Continuous b' := continuous_pi (fun k => (continuous_apply (e k)).comp hb)
  have he (f : κ → ℝ) : ∑ k : Fin (n + 1), f (e k) = ∑ k : κ, f k := e.sum_comp f
  have horth' (i j : I) : ∑ k, (a' i k - a' j k) * (b' i k - b' j k) = 0 := by
    dsimp [a', b']
    rw [he (fun k => (a i k - a j k) * (b i k - b j k))]
    exact horth i j
  have hinc' (i j : I) : (∑ k, (b' i k - b' j k)^2) ≤ ∑ k, (a' i k - a' j k)^2 := by
    dsimp [a', b']
    rw [he (fun k => (b i k - b j k)^2), he (fun k => (a i k - a j k)^2)]
    exact hinc i j
  have hpres : MeasurePreserving E (standardGaussianProduct (n + 1)) (gaussianCoordinates κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have hpoint (c : I → κ → ℝ) (z : Fin (n + 1) → ℝ) :
      gaussianSup m c (E z) = supProcess m (fun i k => c i (e k)) z := by
    unfold gaussianSup supProcess
    congr 1
    congr 1
    funext i
    dsimp [gaussianAffine, affineProcess]
    rw [← he (fun k => c i k * E z k)]
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [← hpres.integral_comp' (gaussianSup m b), ← hpres.integral_comp' (gaussianSup m a)]
  simp_rw [hpoint]
  exact gaussian_supProcess_comparison hm ha' hb' horth' hinc'

end ArbitraryCoordinates
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_QuadraticCoeff
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
namespace SKGap
section GaussianQuadratic
variable {ι : Type*} [Fintype ι]

lemma sum_coord_sq (w : EuclideanSpace ℝ ι) : ∑ i, (w i)^2 = ‖w‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

lemma sum_outer_sq (w v : ι → ℝ) :
    (∑ i, ∑ k, (w i * w k - v i * v k)^2) =
      (∑ i, w i ^ 2)^2 + (∑ i, v i ^ 2)^2 - 2 * (∑ i, w i * v i)^2 := by
  simp_rw [show ∀ i k, (w i * w k - v i * v k)^2 =
    w i ^ 2 * w k ^ 2 + v i ^ 2 * v k ^ 2 - 2 * (w i * v i) * (w k * v k) by
      intros; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

lemma quadraticCoeff_increment (r : ℝ) (hr : 0 ≤ r) (w v : EuclideanSpace ℝ ι) :
    (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) =
      2 * r * (‖w‖^4 + ‖v‖^4 - 2 * (∑ i, w i * v i)^2) := by
  rw [Fintype.sum_sum_type]
  simp only [quadraticCoeff, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type]
  simp_rw [show ∀ i k, (Real.sqrt (2*r) * w i * w k -
      Real.sqrt (2*r) * v i * v k)^2 = 2*r*(w i*w k-v i*v k)^2 by
    intro i k
    calc
      _ = (Real.sqrt (2*r))^2 * (w i*w k-v i*v k)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]]
  simp_rw [← Finset.mul_sum]
  rw [sum_outer_sq, sum_coord_sq, sum_coord_sq]
  ring

lemma linearCoeff_increment (r : ℝ) (hr : 0 ≤ r) (w v : EuclideanSpace ℝ ι) :
    (∑ k, (linearCoeff r w k - linearCoeff r v k)^2) =
      4 * r * (‖w‖^4 + ‖v‖^4 - 2 * ‖w‖ * ‖v‖ * (∑ i, w i * v i)) := by
  rw [Fintype.sum_sum_type]
  simp only [linearCoeff, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, zero_add]
  simp_rw [show ∀ i, (2 * Real.sqrt r * ‖w‖ * w i -
      2 * Real.sqrt r * ‖v‖ * v i)^2 =
      4*r*(‖w‖^2*(w i)^2 + ‖v‖^2*(v i)^2 - 2*‖w‖*‖v‖*(w i*v i)) by
    intro i
    calc
      _ = 4*(Real.sqrt r)^2*(‖w‖^2*(w i)^2 + ‖v‖^2*(v i)^2 -
          2*‖w‖*‖v‖*(w i*v i)) := by ring
      _ = _ := by rw [Real.sq_sqrt hr]]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [sum_coord_sq]
  ring

theorem quadratic_linear_increment_difference (r : ℝ) (hr : 0 ≤ r)
    (w v : EuclideanSpace ℝ ι) :
    (∑ k, (linearCoeff r w k - linearCoeff r v k)^2) -
      (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) =
      2*r*((‖w‖^2 - ‖v‖^2)^2 +
        2*(‖w‖*‖v‖ - ∑ i, w i*v i)^2) := by
  rw [linearCoeff_increment r hr, quadraticCoeff_increment r hr]
  ring

theorem quadratic_linear_increment_le (r : ℝ) (hr : 0 ≤ r)
    (w v : EuclideanSpace ℝ ι) :
    (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) ≤
      ∑ k, (linearCoeff r w k - linearCoeff r v k)^2 := by
  have h := quadratic_linear_increment_difference r hr w v
  have : 0 ≤ 2*r*((‖w‖^2 - ‖v‖^2)^2 +
      2*(‖w‖*‖v‖ - ∑ i, w i*v i)^2) := by positivity
  linarith

lemma quadratic_linear_orthogonal (r : ℝ) (w v : EuclideanSpace ℝ ι) :
    ∑ k, (linearCoeff r w k - linearCoeff r v k) *
      (quadraticCoeff r w k - quadraticCoeff r v k) = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [linearCoeff, quadraticCoeff, sub_self, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero]

omit [Fintype ι] in
lemma continuous_quadraticCoeff (r : ℝ) : Continuous (quadraticCoeff (ι := ι) r) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ik =>
    exact ((continuous_const.mul (PiLp.continuous_apply 2 (fun _ : ι => ℝ) ik.1)).mul
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) ik.2))
  | inr i => exact continuous_const

lemma continuous_linearCoeff (r : ℝ) : Continuous (linearCoeff (ι := ι) r) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ik => exact continuous_const
  | inr i => exact (continuous_const.mul continuous_norm).mul (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)

end GaussianQuadratic
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianQuadraticSupComparison
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
namespace SKGap
section QuadraticComparison
variable {I ι : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype ι] [Nonempty ι]

theorem gaussian_quadraticSup_comparison {m : I → ℝ}
    {w : I → EuclideanSpace ℝ ι} (hm : Continuous m) (hw : Continuous w)
    {r : ℝ} (hr : 0 ≤ r) (z : ℝ) :
    (∫ g, gaussianSup m (fun i k => z * quadraticCoeff r (w i) k) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
    ∫ g, gaussianSup m (fun i k => z * linearCoeff r (w i) k) g
      ∂gaussianCoordinates (MatrixCoordinates ι) := by
  have hc {q : EuclideanSpace ℝ ι → MatrixCoordinates ι → ℝ} (hq : Continuous q) :
      Continuous (fun i k => z * q (w i) k) := by
    apply continuous_pi
    intro k
    exact continuous_const.mul ((continuous_apply k).comp (hq.comp hw))
  apply gaussianSup_comparison hm (hc (continuous_linearCoeff r))
    (hc (continuous_quadraticCoeff r))
  · intro i j
    simp_rw [← mul_sub]
    simp_rw [show ∀ k, (z * (linearCoeff r (w i) k - linearCoeff r (w j) k)) *
        (z * (quadraticCoeff r (w i) k - quadraticCoeff r (w j) k)) =
        z^2 * ((linearCoeff r (w i) k - linearCoeff r (w j) k) *
        (quadraticCoeff r (w i) k - quadraticCoeff r (w j) k)) by intros; ring]
    rw [← Finset.mul_sum, quadratic_linear_orthogonal, mul_zero]
  · intro i j
    simp_rw [← mul_sub, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (quadratic_linear_increment_le r hr (w i) (w j))
      (sq_nonneg z)
end QuadraticComparison
end SKGap

namespace SKGap
section SupLipschitz
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I] [Fintype κ]

lemma gaussianAffine_le_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (x : κ → ℝ) (i : I) :
    gaussianAffine m a x i ≤ gaussianSup m a x := by
  obtain ⟨j, hj, hmax⟩ := gaussianSup_attained hm ha x
  rw [hj]
  exact hmax i

lemma gaussianSup_sub_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) (x y : EuclideanSpace ℝ κ) :
    gaussianSup m a x.ofLp - gaussianSup m a y.ofLp ≤ L * ‖x-y‖ := by
  obtain ⟨i, hi, _⟩ := gaussianSup_attained hm ha x.ofLp
  calc
    _ ≤ gaussianAffine m a x.ofLp i - gaussianAffine m a y.ofLp i := by
      rw [hi]
      exact sub_le_sub_left (gaussianAffine_le_gaussianSup hm ha y.ofLp i) _
    _ = inner ℝ (WithLp.toLp 2 (a i)) (x-y) := by
      simp only [gaussianAffine, PiLp.inner_apply, WithLp.ofLp_sub,
        Pi.sub_apply, RCLike.inner_apply, conj_trivial]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ‖WithLp.toLp 2 (a i)‖ * ‖x-y‖ := real_inner_le_norm _ _
    _ ≤ L * ‖x-y‖ := mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _)

theorem gaussianSup_lipschitz {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ≥0}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ (L : ℝ)) :
    LipschitzWith L (fun x : EuclideanSpace ℝ κ => gaussianSup m a x.ofLp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := gaussianSup_sub_le hm ha hL y x
    rw [norm_sub_rev] at h
    linarith
  · exact gaussianSup_sub_le hm ha hL x y

end SupLipschitz
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalSqrt
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
namespace SKGap
section DiagonalGeometry
variable {ι : Type*} [Fintype ι]

lemma diagonalSqrt_norm_sq (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (p : EuclideanSpace ℝ ι) :
    ‖diagonalSqrt a p‖^2 = ∑ i, a i * (p i)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [diagonalSqrt, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (ha i)]

lemma diagonalSqrt_norm_sq_le {a : ι → ℝ} {A : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (p : EuclideanSpace ℝ ι) :
    ‖diagonalSqrt a p‖^2 ≤ A * ‖p‖^2 := by
  rw [diagonalSqrt_norm_sq a ha, ← sum_coord_sq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hA i) (sq_nonneg _))

lemma diagonalSqrt_norm_le_sqrt {a : ι → ℝ} {A : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A)
    {p : EuclideanSpace ℝ ι} (hp : ‖p‖ ≤ 1) :
    ‖diagonalSqrt a p‖ ≤ Real.sqrt A := by
  have h := diagonalSqrt_norm_sq_le ha hA p
  have hp2 : ‖p‖^2 ≤ 1 := by nlinarith [norm_nonneg p]
  have hh := mul_le_mul_of_nonneg_left hp2 hA0
  have hs := Real.sq_sqrt hA0
  have hs0 := Real.sqrt_nonneg A
  nlinarith [norm_nonneg (diagonalSqrt a p)]

omit [Fintype ι] in
lemma continuous_diagonalSqrt (a : ι → ℝ) : Continuous (diagonalSqrt a) := by
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  exact continuous_pi (fun i => continuous_const.mul (PiLp.continuous_apply 2 (fun _ => ℝ) i))

lemma diagonal_sum_mul_le_norm (a : ι → ℝ) (p g : EuclideanSpace ℝ ι) :
    (∑ i, diagonalSqrt a p i * g i) ≤ ‖p‖ * ‖diagonalSqrt a g‖ := by
  have he : (∑ i, diagonalSqrt a p i * g i) = inner ℝ p (diagonalSqrt a g) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [diagonalSqrt, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
    ring
  rw [he]
  exact real_inner_le_norm _ _

lemma quadraticCoeff_norm {r : ℝ} (hr : 0 ≤ r) (w : EuclideanSpace ℝ ι) :
    ‖WithLp.toLp 2 (quadraticCoeff r w)‖ = Real.sqrt (2*r) * ‖w‖^2 := by
  have hsum : (∑ k, (quadraticCoeff r w k)^2) = 2*r*‖w‖^4 := by
    have h := quadraticCoeff_increment r hr w 0
    have h0 : quadraticCoeff r (0 : EuclideanSpace ℝ ι) = 0 := by
      funext k
      cases k <;> simp [quadraticCoeff]
    simpa only [h0, Pi.zero_apply, sub_zero, norm_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0),
      WithLp.ofLp_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero] using h
  have he : ‖WithLp.toLp 2 (quadraticCoeff r w)‖^2 =
      (Real.sqrt (2*r) * ‖w‖^2)^2 := by
    rw [← sum_coord_sq, hsum, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hnon : 0 ≤ Real.sqrt (2*r) * ‖w‖^2 := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 (quadraticCoeff r w))]

end DiagonalGeometry

lemma quadratic_margin {d b : ℝ} (_hd : 0 ≤ d) (hdb : d ≤ b) (hb : b ≤ 1) :
    2*d-d^2 ≤ 1-(1-b)^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hdb) (show 0 ≤ 2-b-d by linarith)]

end SKGap

open Real

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_UnitBall
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
namespace SKGap
lemma quadratic_interpolation {z q v c : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hc : 0 ≤ c) (hqc : q*v ≤ c) {X : ℝ} (hX : X - q*v ≤ c) :
    z*X-z^2*q*v ≤ c := by
  have h1 := mul_le_mul_of_nonneg_left hX hz0
  have h2 := mul_le_mul_of_nonneg_left hqc (mul_nonneg hz0 (sub_nonneg.mpr hz1))
  have h3 := mul_nonneg hc (sq_nonneg (1-z))
  nlinarith only [h1, h2, h3]

section DiagonalProcess
variable {ι : Type*} [Fintype ι]

lemma norm_UnitBall_le (p : UnitBall ι) : ‖(p : EuclideanSpace ℝ ι)‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using p.property

lemma continuous_diagonalOffset (a : ι → ℝ) (z q : ℝ) :
    Continuous (diagonalOffset a z q) := by
  exact continuous_const.mul (((continuous_diagonalSqrt a).comp continuous_subtype_val).norm.pow 2)

lemma continuous_diagonalCoeff {f : EuclideanSpace ℝ ι → MatrixCoordinates ι → ℝ}
    (hf : Continuous f) (a : ι → ℝ) (z : ℝ) :
    Continuous (fun p : UnitBall ι => fun k => z * f (diagonalSqrt a p) k) := by
  apply continuous_pi
  intro k
  exact continuous_const.mul ((continuous_apply k).comp
    (hf.comp ((continuous_diagonalSqrt a).comp continuous_subtype_val)))

lemma integrable_diagonalLinearProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ) :
    Integrable (diagonalLinearProcess r a z q) (gaussianCoordinates (MatrixCoordinates ι)) :=
  integrable_gaussianSup (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_linearCoeff r) a z)

lemma diagonalT_norm {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (g : MatrixCoordinates ι → ℝ) :
    diagonalT r a g = sqrt r * ‖diagonalSqrt a (WithLp.toLp 2 (fun i => g (.inr i)))‖ := by
  unfold diagonalT gaussianQuadratic
  rw [Fintype.sum_sum_type]
  simp only [diagonalWeights, zero_mul, Finset.sum_const_zero, zero_add]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, Real.sqrt_mul hr]
  have he := diagonalSqrt_norm_sq a ha (WithLp.toLp 2 (fun i => g (.inr i)))
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

lemma diagonalWeights_sum (r : ℝ) (a : ι → ℝ) :
    (∑ k, diagonalWeights r a k) = r * ∑ i, a i := by
  simp only [Fintype.sum_sum_type, diagonalWeights, Finset.sum_const_zero, zero_add,
    Finset.mul_sum]

lemma diagonalWeights_sum_sq (r : ℝ) (a : ι → ℝ) :
    (∑ k, (diagonalWeights r a k)^2) = r^2 * ∑ i, (a i)^2 := by
  simp only [Fintype.sum_sum_type, diagonalWeights, zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero, zero_add, mul_pow, Finset.mul_sum]

lemma diagonalT_integrable {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Integrable (diagonalT r a) (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply (memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (diagonalWeights r a)).integrable
    (by norm_num)) ?_).integrable (by norm_num)
  intro g
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (sq_nonneg _)
  cases k <;> simp only [diagonalWeights]
  · exact le_rfl
  · exact mul_nonneg hr (ha _)

lemma diagonalT_fluctuation {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∫ g, |diagonalT r a g - sqrt (r * ∑ i, a i)|
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      sqrt (sqrt (2*r^2 * ∑ i, (a i)^2)) := by
  have hp (g) : 0 ≤ gaussianQuadratic (diagonalWeights r a) g := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (sq_nonneg _)
    cases k <;> simp only [diagonalWeights]
    · exact le_rfl
    · exact mul_nonneg hr (ha _)
  have h := integral_sqrt_fluctuation (gaussianQuadratic_memLp (diagonalWeights r a)) hp
  rw [gaussianQuadratic_mean, gaussianQuadratic_variance,
    diagonalWeights_sum, diagonalWeights_sum_sq, ← mul_assoc] at h
  exact h

lemma diagonalLinearProcess_le {r z q A b : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq : 0 ≤ q)
    (hqb : sqrt q * sqrt A ≤ b) (hb : b ≤ 1)
    (g : MatrixCoordinates ι → ℝ) :
    diagonalLinearProcess r a z q g ≤
      1-(1-b)^2 + 2 * sqrt A * |diagonalT r a g - sqrt q| := by
  unfold diagonalLinearProcess
  apply gaussianSup_le (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_linearCoeff r) a z)
  intro p
  let w := diagonalSqrt a p
  let v := ‖w‖
  have hv0 : 0 ≤ v := norm_nonneg _
  have hv : v ≤ sqrt A := diagonalSqrt_norm_le_sqrt ha hA0 hA (norm_UnitBall_le p)
  have hdot := diagonal_sum_mul_le_norm a (p : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 (fun i => g (.inr i)))
  have hdot' : (∑ i, w i * g (.inr i)) ≤
      ‖diagonalSqrt a (WithLp.toLp 2 (fun i => g (.inr i)))‖ :=
    hdot.trans ((mul_le_mul_of_nonneg_right (norm_UnitBall_le p) (norm_nonneg _)).trans_eq
      (one_mul _))
  have hcoeff : (∑ k, (z * linearCoeff r w k) * g k) =
      2*z*sqrt r*v * (∑ i, w i * g (.inr i)) := by
    simp only [Fintype.sum_sum_type, linearCoeff, mul_zero, zero_mul,
      Finset.sum_const_zero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    ring
  have hlin := mul_le_mul_of_nonneg_left hdot' (show 0 ≤ 2*z*sqrt r*v by positivity)
  have hT := diagonalT_norm hr ha g
  have hlin' : (∑ k, (z * linearCoeff r w k) * g k) ≤ 2*z*v*diagonalT r a g := by
    rw [hcoeff, hT]
    nlinarith only [hlin]
  have hd0 : 0 ≤ z * sqrt q * v := by positivity
  have hzb : z * sqrt q * v ≤ b := by
    calc
      _ ≤ sqrt q * v := by nlinarith [mul_nonneg (sqrt_nonneg q) hv0]
      _ ≤ sqrt q * sqrt A := mul_le_mul_of_nonneg_left hv (sqrt_nonneg q)
      _ ≤ b := hqb
  have hmargin := quadratic_margin hd0 hzb hb
  have hs := sq_sqrt hq
  have hab := le_abs_self (diagonalT r a g - sqrt q)
  have hvz : z*v ≤ sqrt A := (mul_le_of_le_one_left hv0 hz1).trans hv
  have herr : 2*z*v*(diagonalT r a g - sqrt q) ≤
      2*sqrt A*|diagonalT r a g - sqrt q| := by
    exact (mul_le_mul_of_nonneg_left hab (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _))
  change -z^2*q*v^2 + (∑ k, (z * linearCoeff r w k) * g k) ≤ _
  nlinarith only [hlin', hmargin, herr, hs, sq_nonneg (z*v)]

theorem diagonalProcess_expected_margin [Nonempty ι]
    {r z A b : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hqb : sqrt (r * ∑ i, a i) * sqrt A ≤ b) (hb : b ≤ 1) :
    (∫ g, diagonalProcess r a z (r * ∑ i, a i) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-b)^2 + 2*sqrt A * sqrt (sqrt (2*r^2 * ∑ i, (a i)^2)) := by
  let q := r * ∑ i, a i
  have hq : 0 ≤ q := mul_nonneg hr (Finset.sum_nonneg (fun i _ => ha i))
  have hcomp := gaussian_quadraticSup_comparison
    (continuous_diagonalOffset a z q)
    ((continuous_diagonalSqrt a).comp continuous_subtype_val) hr z
  have hfluct := diagonalT_fluctuation hr ha
  have hi : Integrable (fun g => |diagonalT r a g - sqrt q|)
      (gaussianCoordinates (MatrixCoordinates ι)) :=
    ((diagonalT_integrable hr ha).sub (integrable_const _)).abs
  have hbound : (∫ g, diagonalLinearProcess r a z q g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-b)^2 + 2*sqrt A *
        (∫ g, |diagonalT r a g - sqrt q| ∂gaussianCoordinates (MatrixCoordinates ι)) := by
    calc
      _ ≤ ∫ g, (1-(1-b)^2 + 2*sqrt A*|diagonalT r a g - sqrt q|)
          ∂gaussianCoordinates (MatrixCoordinates ι) :=
        integral_mono (integrable_diagonalLinearProcess r a z q)
          ((integrable_const _).add (hi.const_mul _))
          (diagonalLinearProcess_le hr ha hA hA0 hz0 hz1 hq hqb hb)
      _ = _ := by rw [integral_add (integrable_const _) (hi.const_mul _),
                      integral_const, probReal_univ, one_smul, integral_const_mul]
  exact hcomp.trans (hbound.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hfluct (show 0 ≤ 2*sqrt A by positivity))))

lemma diagonalProcess_lipschitz {r z A : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz : 0 ≤ z) (q : ℝ) :
    LipschitzWith (Real.toNNReal (z * sqrt (2*r) * A))
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
        diagonalProcess r a z q g.ofLp) := by
  apply gaussianSup_lipschitz (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z)
  intro p
  have hsq := diagonalSqrt_norm_sq_le ha hA (p : EuclideanSpace ℝ ι)
  have hp2 : ‖(p : EuclideanSpace ℝ ι)‖^2 ≤ 1 := by
    nlinarith [norm_UnitBall_le p, norm_nonneg (p : EuclideanSpace ℝ ι)]
  have hw : ‖diagonalSqrt a p‖^2 ≤ A :=
    hsq.trans ((mul_le_mul_of_nonneg_left hp2 hA0).trans_eq (mul_one A))
  have he : WithLp.toLp 2 (fun k => z * quadraticCoeff r (diagonalSqrt a p) k) =
      z • WithLp.toLp 2 (quadraticCoeff r (diagonalSqrt a p)) := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz, quadraticCoeff_norm hr,
    Real.toNNReal_of_nonneg (by positivity)]
  simpa only [mul_assoc, NNReal.coe_mk] using
    mul_le_mul_of_nonneg_left hw (show 0 ≤ z * sqrt (2*r) by positivity)

theorem diagonalProcess_path_le {r A q c : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hqc : q*A ≤ c)
    {g : MatrixCoordinates ι → ℝ} (hg : diagonalProcess r a 1 q g ≤ c)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    diagonalProcess r a z q g ≤ c := by
  apply gaussianSup_le (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z)
  intro p
  let w := diagonalSqrt a p
  let v := ‖w‖^2
  let X := ∑ k, quadraticCoeff r w k * g k
  have hp2 : ‖(p : EuclideanSpace ℝ ι)‖^2 ≤ 1 := by
    nlinarith [norm_UnitBall_le p, norm_nonneg (p : EuclideanSpace ℝ ι)]
  have hv : v ≤ A := (diagonalSqrt_norm_sq_le ha hA _).trans
    ((mul_le_mul_of_nonneg_left hp2 hA0).trans_eq (mul_one A))
  have hqv : q*v ≤ c := (mul_le_mul_of_nonneg_left hv hq).trans hqc
  have hX : X - q*v ≤ c := by
    have h := (gaussianAffine_le_gaussianSup (continuous_diagonalOffset a 1 q)
      (continuous_diagonalCoeff (continuous_quadraticCoeff r) a 1) g p).trans hg
    simp only [gaussianAffine, diagonalOffset, one_mul, one_pow, neg_mul] at h
    simpa only [sub_eq_add_neg, add_comm, X, v, w] using h
  have h := quadratic_interpolation hz0 hz1 hc hqv hX
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gaussianAffine, diagonalOffset, X, v, w, Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

end DiagonalProcess
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalSum
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
section MatrixScale
variable {ι : Type*} [Fintype ι]

lemma diagonal_sum_le {a : ι → ℝ} {A : ℝ} (hA : ∀ i, a i ≤ A) :
    (∑ i, a i) ≤ (Fintype.card ι : ℝ) * A := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)

lemma diagonal_sq_sum_le {a : ι → ℝ} {A : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    (∑ i, (a i)^2) ≤ (Fintype.card ι : ℝ) * A^2 :=
  diagonal_sum_le (fun i => by nlinarith [ha i, hA i])

lemma scaled_mean_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (hA : ∀ i, a i ≤ A) :
    (j / (Fintype.card ι : ℝ)) * (∑ i, a i) ≤ j*A := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left (diagonal_sum_le hA) (div_nonneg hj hn.le)
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

lemma scaled_variance_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    2*(j / (Fintype.card ι : ℝ))^2 * (∑ i, (a i)^2) ≤
      2*j^2*A^2 / (Fintype.card ι : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left (diagonal_sq_sum_le ha hA)
    (show 0 ≤ 2*(j / (Fintype.card ι : ℝ))^2 by positivity)
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

lemma scaled_sqrt_mean_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A) :
    sqrt ((j / (Fintype.card ι : ℝ)) * (∑ i, a i)) * sqrt A ≤ sqrt j * A := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hq : 0 ≤ (j / (Fintype.card ι : ℝ)) * ∑ i, a i :=
    mul_nonneg (div_nonneg hj hn) (Finset.sum_nonneg (fun i _ => ha i))
  rw [← sqrt_mul hq]
  calc
    _ ≤ sqrt (j * A^2) := sqrt_le_sqrt (by
      have h := mul_le_mul_of_nonneg_right (scaled_mean_bound hj hA) hA0
      nlinarith only [h])
    _ = sqrt j * A := by rw [sqrt_mul hj, sqrt_sq hA0]

lemma subcritical_endpoint_margin {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b^2 ≤ 1 - (1-b)^2/2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (show 0 ≤ 3*b+1 by positivity)]

lemma scaled_qA_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hsub : sqrt j * A ≤ 1) :
    ((j / (Fintype.card ι : ℝ)) * (∑ i, a i))*A ≤
      1-(1-sqrt j*A)^2/2 := by
  have h := mul_le_mul_of_nonneg_right (scaled_mean_bound hj hA) hA0
  have hm := subcritical_endpoint_margin (show 0 ≤ sqrt j*A by positivity) hsub
  have he : (sqrt j*A)^2 = j*A^2 := by rw [mul_pow, sq_sqrt hj]
  rw [he] at hm
  nlinarith only [h, hm]

end MatrixScale

end SKGap

namespace SKGap
section DiagonalProbability
open MeasureTheory ProbabilityTheory Real Set Filter
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scaled_diagonal_expected_margin {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hsub : sqrt j*A ≤ 1) :
    (∫ g, diagonalProcess (j/(Fintype.card ι:ℝ)) a 1
      ((j/(Fintype.card ι:ℝ))*∑ i, a i) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-sqrt j*A)^2 +
        2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) := by
  have h := diagonalProcess_expected_margin (div_nonneg hj (by positivity)) ha hA hA0
    (by norm_num : (0:ℝ) ≤ 1) le_rfl (scaled_sqrt_mean_bound hj ha hA hA0) hsub
  exact h.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (sqrt_le_sqrt
      (scaled_variance_bound (j := j) ha hA))) (show 0 ≤ 2*sqrt A by positivity)) _)

theorem scaled_diagonal_path_tail {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1,
        1-(1-sqrt j*A)^2/2 < diagonalProcess (j/(Fintype.card ι:ℝ)) a z
          ((j/(Fintype.card ι:ℝ))*∑ i, a i) g} ≤
      Real.exp (-((1-sqrt j*A)^2)^2 * (Fintype.card ι:ℝ) / (16*π^2*j*A^2)) := by
  let r := j/(Fintype.card ι:ℝ)
  let q := r*∑ i, a i
  let δ := (1-sqrt j*A)^2
  let c := 1-δ/2
  let P := diagonalProcess r a 1 q
  have hn : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hq : 0 ≤ q := mul_nonneg hr.le (Finset.sum_nonneg (fun i _ => ha i))
  have hd : 0 < δ := sq_pos_of_pos (sub_pos.mpr hsub)
  have hd1 : δ ≤ 1 := by
    dsimp [δ]
    have hb : 0 ≤ sqrt j*A := by positivity
    nlinarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hqc : q*A ≤ c := scaled_qA_bound hj.le hA hA0.le hsub.le
  have hmean : (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 1-3*δ/4 := by
    have h := scaled_diagonal_expected_margin hj.le ha hA hA0.le hsub.le
    change (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 1-δ+_ at h
    change _ ≤ δ/4 at herr
    linarith
  have hlip := diagonalProcess_lipschitz hr.le ha hA hA0.le (by norm_num : (0:ℝ) ≤ 1) q
  have hL : 0 < Real.toNNReal (1*sqrt (2*r)*A) := by
    rw [Real.toNNReal_pos]
    positivity
  have htail := gaussianProduct_upper_tail_lipschitz hlip hL (show 0 ≤ δ/4 by positivity)
  have hset : {g | ∃ z ∈ Icc (0:ℝ) 1, c < diagonalProcess r a z q g} ⊆
      {g | δ/4 ≤ P g - ∫ y, P y ∂gaussianCoordinates (MatrixCoordinates ι)} := by
    rintro g ⟨z, hz, hg⟩
    have hgc : c < P g := by
      by_contra h
      have hpath := diagonalProcess_path_le ha hA hA0.le hq hc hqc
        (le_of_not_gt h) hz.1 hz.2
      exact (not_lt_of_ge hpath) hg
    change δ/4 ≤ _
    dsimp [c] at hgc
    linarith
  refine (measureReal_mono hset).trans (htail.trans_eq ?_)
  congr 1
  rw [Real.coe_toNNReal _ (by positivity)]
  have hs : (sqrt (2*r))^2 = 2*r := sq_sqrt (by positivity)
  simp only [one_mul]
  rw [mul_pow, hs]
  dsimp [δ, r]
  field_simp
  ring

end DiagonalProbability
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalTMemLp
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
section GOEProbability
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma diagonalT_memLp {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    MemLp (diagonalT r a) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (diagonalWeights r a)).integrable
    (by norm_num))
  intro g
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (sq_nonneg _)
  cases k <;> simp only [diagonalWeights]
  · exact le_rfl
  · exact mul_nonneg hr (ha _)

omit [Nonempty ι] in
lemma diagonalT_mean_le {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∫ g, diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      sqrt (r * ∑ i, a i) := by
  have he (g : MatrixCoordinates ι → ℝ) : (diagonalT r a g)^2 =
      gaussianQuadratic (diagonalWeights r a) g := by
    apply sq_sqrt
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (sq_nonneg _)
    cases k <;> simp only [diagonalWeights]
    · exact le_rfl
    · exact mul_nonneg hr (ha _)
  have h := integral_abs_le_sqrt_sq (diagonalT_memLp hr ha)
  simp_rw [he, abs_of_nonneg (show 0 ≤ diagonalT r a _ from sqrt_nonneg _)] at h
  have hm : (∫ g, gaussianQuadratic (diagonalWeights r a) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) = r * ∑ i, a i := by
    simpa only [gaussianCoordinates, diagonalWeights_sum] using gaussianQuadratic_mean (diagonalWeights r a)
  rwa [hm] at h

theorem goe_expected_top {j : ℝ} (hj : 0 ≤ j) :
    (∫ g, diagonalProcess (j/(Fintype.card ι:ℝ)) (fun _ : ι => 1) 1 0 g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 2*sqrt j := by
  let r := j/(Fintype.card ι:ℝ)
  let a : ι → ℝ := fun _ => 1
  have hr : 0 ≤ r := div_nonneg hj (by positivity)
  have ha : ∀ i, 0 ≤ a i := by intro; norm_num [a]
  have hc := gaussian_quadraticSup_comparison (continuous_diagonalOffset a 1 0)
    ((continuous_diagonalSqrt a).comp continuous_subtype_val) hr 1
  change (∫ g, diagonalProcess r a 1 0 g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
    (∫ g, diagonalLinearProcess r a 1 0 g ∂gaussianCoordinates (MatrixCoordinates ι)) at hc
  have hb (g) : diagonalLinearProcess r a 1 0 g ≤ 2*diagonalT r a g := by
    have h := diagonalLinearProcess_le (A := 1) (b := 0) hr ha
      (by intro; exact le_rfl) zero_le_one (by norm_num : (0:ℝ) ≤ 1) le_rfl
      le_rfl (by norm_num) zero_le_one g
    simpa only [sub_zero, one_pow, sub_self, sqrt_zero, sqrt_one, mul_one,
      abs_of_nonneg (show 0 ≤ diagonalT r a g from sqrt_nonneg _), zero_add] using h
  have hi := diagonalT_integrable hr ha
  calc
    _ ≤ ∫ g, diagonalLinearProcess r a 1 0 g
        ∂gaussianCoordinates (MatrixCoordinates ι) := hc
    _ ≤ ∫ g, 2*diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι) :=
      integral_mono (integrable_diagonalLinearProcess r a 1 0) (hi.const_mul 2) hb
    _ = 2 * ∫ g, diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι) :=
      integral_const_mul _ _
    _ ≤ 2*sqrt (r * ∑ i, a i) := mul_le_mul_of_nonneg_left (diagonalT_mean_le hr ha) (by norm_num)
    _ = 2*sqrt j := by
      have hn : (Fintype.card ι:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [a, r, hn]

lemma gaussianCoordinates_preserving_neg {κ : Type*} [Fintype κ] :
    MeasurePreserving (fun g : κ → ℝ => -g) (gaussianCoordinates κ)
      (gaussianCoordinates κ) := by
  apply measurePreserving_pi (f := fun _ => fun x : ℝ => -x)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  intro i
  exact ⟨by fun_prop, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

theorem goe_top_tail {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt j+ε < diagonalProcess (j/(Fintype.card ι:ℝ)) (fun _ : ι => 1) 1 0 g} ≤
      Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j)) := by
  let r := j/(Fintype.card ι:ℝ)
  let P := diagonalProcess r (fun _ : ι => 1) 1 0
  have hn : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hL := diagonalProcess_lipschitz (a := fun _ : ι => 1) hr.le (fun _ => zero_le_one)
    (fun _ => le_rfl) zero_le_one (by norm_num : (0:ℝ) ≤ 1) 0
  have hLp : 0 < Real.toNNReal (1*sqrt (2*r)*1) := by
    rw [Real.toNNReal_pos]; positivity
  have ht := gaussianProduct_upper_tail_lipschitz hL hLp hε
  have hm := goe_expected_top (ι := ι) hj.le
  have hs : {g | 2*sqrt j+ε < P g} ⊆
      {g | ε ≤ P g - ∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)} := by
    intro g hg
    change ε ≤ P g - ∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)
    change _ < P g at hg
    change (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 2*sqrt j at hm
    linarith
  exact (measureReal_mono hs).trans (ht.trans_eq (by
    congr 1
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [one_mul, mul_one]
    rw [sq_sqrt (by positivity)]
    dsimp [r]
    field_simp))

end GOEProbability
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixQuad
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixOperator_apply (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (i : ι) :
    matrixOperator M p i = ∑ k, M i k * p k := by
  rfl

lemma matrixQuad_inner (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad M p = inner ℝ p (matrixOperator M p) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixOperator_apply,
    matrixQuad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma matrixQuad_smul (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (c : ℝ) :
    matrixQuad M (c • p) = c^2 * matrixQuad M p := by
  simp only [matrixQuad, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_symm (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g).IsHermitian := by
  ext i k
  simp [goeMatrix, add_comm]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_neg (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    goeMatrix r (-g) = -goeMatrix r g := by
  ext i k
  simp only [goeMatrix, Pi.neg_apply, Matrix.neg_apply]
  ring

omit [DecidableEq ι] in
lemma goeMatrix_quad (r : ℝ) (g : MatrixCoordinates ι → ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (goeMatrix r g) p =
      ∑ i, ∑ k, sqrt (2*r) * p i * p k * g (.inl (i,k)) := by
  have hs : (∑ i, ∑ k, p i * g (.inl (k,i)) * p k) =
      ∑ i, ∑ k, p i * g (.inl (i,k)) * p k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = sqrt (2*r)/2 * ((∑ i, ∑ k, p i * g (.inl (i,k)) * p k) +
        ∑ i, ∑ k, p i * g (.inl (k,i)) * p k) := by
      simp only [matrixQuad, goeMatrix, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [hs]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma matrixOperator_norm_le_of_quad {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R)
    (hq : ∀ p : EuclideanSpace ℝ ι, ‖p‖ ≤ 1 → |matrixQuad M p| ≤ R) :
    ‖matrixOperator M‖ ≤ R := by
  have hs : (matrixOperator M).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := matrixOperator M) hs]
  apply ciSup_le
  intro p
  by_cases hp : p = 0
  · simp [hp, ContinuousLinearMap.rayleighQuotient, hR]
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hunit : ‖‖p‖⁻¹ • p‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp0, inv_mul_cancel₀ hp0.ne']
  have hh := hq (‖p‖⁻¹ • p) hunit
  rw [matrixQuad_smul, abs_mul, abs_pow, abs_inv, abs_of_pos hp0] at hh
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, real_inner_comm, ← matrixQuad_inner, abs_div,
    abs_pow, abs_of_pos hp0, inv_pow, div_eq_mul_inv, mul_comm, abs_mul, abs_inv] using hh

end SKGap

namespace SKGap
section GOEEvents
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma goeMatrix_quad_coeff (r : ℝ) (g : MatrixCoordinates ι → ℝ)
    (p : EuclideanSpace ℝ ι) :
    matrixQuad (goeMatrix r g) p = ∑ k, quadraticCoeff r p k * g k := by
  rw [goeMatrix_quad, Fintype.sum_sum_type]
  simp only [quadraticCoeff, zero_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_prod_type]

omit [DecidableEq ι] [Nonempty ι] in
lemma diagonal_affine_matrix (r z q : ℝ) (a : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) (p : UnitBall ι) :
    gaussianAffine (diagonalOffset a z q)
      (fun p k => z * quadraticCoeff r (diagonalSqrt a p) k) g p =
        z * matrixQuad (goeMatrix r g) (diagonalSqrt a p) -
          z^2*q*‖diagonalSqrt a p‖^2 := by
  rw [goeMatrix_quad_coeff]
  simp only [gaussianAffine, diagonalOffset, Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma diagonalSqrt_one (p : EuclideanSpace ℝ ι) :
    diagonalSqrt (fun _ : ι => 1) p = p := by
  ext i
  simp [diagonalSqrt]

omit [DecidableEq ι] [Nonempty ι] in
lemma goe_quad_le_top (r : ℝ) (g : MatrixCoordinates ι → ℝ)
    (p : EuclideanSpace ℝ ι) (hp : ‖p‖ ≤ 1) :
    matrixQuad (goeMatrix r g) p ≤ diagonalProcess r (fun _ : ι => 1) 1 0 g := by
  let p' : UnitBall ι := ⟨p, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp⟩
  have h := gaussianAffine_le_gaussianSup (continuous_diagonalOffset (fun _ : ι => 1) 1 0)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) (fun _ : ι => 1) 1) g p'
  rw [diagonal_affine_matrix, diagonalSqrt_one] at h
  simpa only [one_mul, mul_zero, zero_mul, sub_zero, diagonalProcess, p'] using h

omit [DecidableEq ι] [Nonempty ι] in
lemma matrixQuad_neg (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (-M) p = -matrixQuad M p := by
  simp [matrixQuad, Finset.sum_neg_distrib]

omit [Nonempty ι] in
lemma goe_norm_le_of_top {r R : ℝ} (hR : 0 ≤ R) (g : MatrixCoordinates ι → ℝ)
    (hpos : diagonalProcess r (fun _ : ι => 1) 1 0 g ≤ R)
    (hneg : diagonalProcess r (fun _ : ι => 1) 1 0 (-g) ≤ R) :
    ‖matrixOperator (goeMatrix r g)‖ ≤ R := by
  apply matrixOperator_norm_le_of_quad (goeMatrix_symm r g) hR
  intro p hp
  apply abs_le.mpr
  constructor
  · have h := (goe_quad_le_top r (-g) p hp).trans hneg
    rw [goeMatrix_neg, matrixQuad_neg] at h
    linarith
  · exact (goe_quad_le_top r g p hp).trans hpos

theorem goe_norm_tail {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt j+ε < ‖matrixOperator (goeMatrix (j/(Fintype.card ι:ℝ)) g)‖} ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j)) := by
  let r := j/(Fintype.card ι:ℝ)
  let R := 2*sqrt j+ε
  let P := diagonalProcess r (fun _ : ι => 1) 1 0
  let E : Set (MatrixCoordinates ι → ℝ) := {g | R < P g}
  have hc : Continuous P := continuous_gaussianSup
    (continuous_diagonalOffset (fun _ : ι => 1) 1 0)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) (fun _ : ι => 1) 1)
  have hm : MeasurableSet E := measurableSet_lt measurable_const hc.measurable
  have hp := goe_top_tail (ι := ι) hj hε
  have hn : (gaussianCoordinates (MatrixCoordinates ι)).real {g | R < P (-g)} =
      (gaussianCoordinates (MatrixCoordinates ι)).real E := by
    exact congrArg ENNReal.toReal (gaussianCoordinates_preserving_neg.measure_preimage hm.nullMeasurableSet)
  have hs : {g : MatrixCoordinates ι → ℝ | R < ‖matrixOperator (goeMatrix r g)‖} ⊆ E ∪ {g | R < P (-g)} := by
    intro g hg
    by_contra hh
    have hh' : ¬ R < P g ∧ ¬ R < P (-g) := by simpa only [Set.mem_union, E, Set.mem_ofPred_eq, not_or] using hh
    exact (not_lt_of_ge (goe_norm_le_of_top (by dsimp [R]; positivity) g
      (le_of_not_gt hh'.1) (le_of_not_gt hh'.2))) hg
  calc
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real (E ∪ {g | R < P (-g)}) := measureReal_mono hs
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real E +
        (gaussianCoordinates (MatrixCoordinates ι)).real {g | R < P (-g)} := measureReal_union_le _ _
    _ = 2*(gaussianCoordinates (MatrixCoordinates ι)).real E := by rw [hn]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

end GOEEvents
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
-- module Solutions.OAIQ072_SK.SKGap_Stability_StabilityMatrix
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
section GOEPath
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stabilityMatrix_quad (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (z q : ℝ)
    (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (stabilityMatrix a z q M) p =
      ‖p‖^2 + z^2*q*‖diagonalSqrt a p‖^2 - z*matrixQuad M (diagonalSqrt a p) := by
  rw [diagonalSqrt_norm_sq a ha, ← sum_coord_sq p]
  simp only [matrixQuad, stabilityMatrix, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  · simp only [Finset.mul_sum, diagonalSqrt]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma diagonalProcess_coercive {r z q c : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) {g : MatrixCoordinates ι → ℝ}
    (hg : diagonalProcess r a z q g ≤ 1-c) (p : EuclideanSpace ℝ ι) :
    c*‖p‖^2 ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p := by
  by_cases hp : p = 0
  · simp [hp, matrixQuad]
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  let v : EuclideanSpace ℝ ι := ‖p‖⁻¹ • p
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp0, inv_mul_cancel₀ hp0.ne']
  let v' : UnitBall ι := ⟨v, by simp [Metric.mem_closedBall, hv]⟩
  have h := (gaussianAffine_le_gaussianSup (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z) g v').trans hg
  rw [diagonal_affine_matrix] at h
  have hs := stabilityMatrix_quad a ha z q (goeMatrix r g) v
  change z*matrixQuad (goeMatrix r g) (diagonalSqrt a v) -
    z^2*q*‖diagonalSqrt a v‖^2 ≤ 1-c at h
  rw [hv, one_pow] at hs
  have hc : c ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) v := by linarith
  rw [show v = ‖p‖⁻¹ • p from rfl, matrixQuad_smul] at hc
  have hc' : c ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p / ‖p‖^2 := by
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using hc
  exact (le_div_iff₀ (sq_pos_of_pos hp0)).mp hc'

variable [Nonempty ι]

theorem goe_diagonal_matrix_path_tail {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1, ∃ p : EuclideanSpace ℝ ι,
        matrixQuad (stabilityMatrix a z ((j/(Fintype.card ι:ℝ))*∑ i, a i)
          (goeMatrix (j/(Fintype.card ι:ℝ)) g)) p < (1-sqrt j*A)^2/2 * ‖p‖^2} ≤
      Real.exp (-((1-sqrt j*A)^2)^2 * (Fintype.card ι:ℝ) / (16*π^2*j*A^2)) := by
  apply (measureReal_mono ?_).trans (scaled_diagonal_path_tail hj hA0 ha hA hsub herr)
  rintro g ⟨z, hz, p, hp⟩
  refine ⟨z, hz, ?_⟩
  by_contra hh
  have hc := diagonalProcess_coercive ha (le_of_not_gt hh) p
  exact (not_lt_of_ge hc) hp

end GOEPath
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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathDiagonal
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
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stabilityMatrix_path_rep (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {z : ℝ}
    (hz : 0 ≤ z) (q : ℝ) (M : Matrix ι ι ℝ) :
    stabilityMatrix a z q M = 1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z := by
  ext i k
  simp only [stabilityMatrix,Matrix.sub_apply,pathDiagonal,pathShift,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply]
  by_cases hik : i=k
  · subst k
    simp only [↓reduceIte]
    have hz2 := sq_sqrt hz
    have ha2 := sq_sqrt (ha i)
    ring_nf
    rw [hz2,ha2]
    ring
  · simp only [hik,↓reduceIte,sub_zero]
    have hz2 := sq_sqrt hz
    nlinarith only [congrArg (fun x : ℝ => x*sqrt (a i)*M i k*sqrt (a k)) hz2]

lemma pathDiagonal_opNorm {a : ι → ℝ} {A z : ℝ} (_hA0 : 0 ≤ A)
    (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) :
    opNorm (pathDiagonal a z) ≤ sqrt A := by
  apply opNorm_diagonal_le (sqrt_nonneg _)
  intro i
  rw [abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  have hz1 : sqrt z ≤ 1 := by simpa using sqrt_le_sqrt hz.2
  exact (mul_le_mul hz1 (sqrt_le_sqrt (hA i)) (sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma pathShift_opNorm {z q : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) :
    opNorm (pathShift (ι := ι) z q) ≤ q := by
  apply opNorm_diagonal_le hq
  intro i
  rw [abs_of_nonneg (mul_nonneg hz.1 hq)]
  exact (mul_le_mul_of_nonneg_right hz.2 hq).trans_eq (one_mul _)

lemma stabilityMatrix_opNorm {a : ι → ℝ} {A z q R : ℝ} {M : Matrix ι ι ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) (hq : 0 ≤ q) (hM : opNorm M ≤ R) :
    opNorm (stabilityMatrix a z q M) ≤ 1+A*(R+q) := by
  rw [stabilityMatrix_path_rep a ha hz.1 q M]
  have hD := pathDiagonal_opNorm hA0 hA hz
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hD 2
    rwa [sq_sqrt hA0] at h
  apply (real_sandwich_stability_norm _ _ _).trans
  apply add_le_add le_rfl
  exact mul_le_mul hd2 (add_le_add hM (pathShift_opNorm hz hq))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) hA0

variable [Nonempty ι]
omit [DecidableEq ι] in
lemma diagonal_mean_bounds {j A : ℝ} {a : ι → ℝ} (hj : 0 ≤ j)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    0 ≤ (j/(Fintype.card ι:ℝ))*∑ i, a i ∧
    (j/(Fintype.card ι:ℝ))*∑ i, a i ≤ j*A := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨mul_nonneg (div_nonneg hj hn.le) (Finset.sum_nonneg (fun i _ => ha i)),?_⟩
  have hs : (∑ i, a i) ≤ (Fintype.card ι:ℝ)*A := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hA i)
  calc
    _ ≤ (j/(Fintype.card ι:ℝ))*((Fintype.card ι:ℝ)*A) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hj hn.le)
    _ = _ := by field_simp

theorem goe_path_spectral_tail {j A ε : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (hε : 0 ≤ ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    let r := j/(Fintype.card ι:ℝ)
    let q := r*∑ i, a i
    let R := 2*sqrt j+ε
    let c := (1-sqrt j*A)^2/2
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1,
        ¬(opNorm (goeMatrix r g) < R+1 ∧
          c/2 < _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) ∧
          -(2+A*(R+j*A)) < _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a z q (goeMatrix r g))))} ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j))+
        Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) := by
  intro r q R c
  let E := {g : MatrixCoordinates ι → ℝ | R < opNorm (goeMatrix r g)}
  let F := {g : MatrixCoordinates ι → ℝ | ∃ z ∈ Icc (0:ℝ) 1, ∃ p : EuclideanSpace ℝ ι,
    matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p < c*‖p‖^2}
  have hc0 : 0 < c := by
    have h : 0 < 1-sqrt j*A := sub_pos.mpr hsub
    dsimp [c]; positivity
  have hq := diagonal_mean_bounds hj.le ha hA
  have hs : {g | ∃ z ∈ Icc (0:ℝ) 1,
        ¬(opNorm (goeMatrix r g) < R+1 ∧
          c/2 < _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) ∧
          -(2+A*(R+j*A)) < _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a z q (goeMatrix r g))))} ⊆ E ∪ F := by
    rintro g ⟨z,hz,hfail⟩
    by_contra hn
    have hE : opNorm (goeMatrix r g) ≤ R := by
      by_contra hh
      exact hn (Or.inl (lt_of_not_ge hh))
    have hF (p : EuclideanSpace ℝ ι) : c*‖p‖^2 ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p := by
      by_contra hh
      exact hn (Or.inr ⟨z,hz,p,lt_of_not_ge hh⟩)
    have hl : c ≤ _root_.OAI.SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a z q (goeMatrix r g))) :=
      lowerRayleigh_lift_ge hF
    have hnorm := stabilityMatrix_opNorm ha hA hA0.le hz hq.1 hE
    have hbound : opNorm (stabilityMatrix a z q (goeMatrix r g)) ≤ 1+A*(R+j*A) :=
      hnorm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hq.2) hA0.le))
    have hu := lowerRayleigh_neg_lift_ge (stabilityMatrix a z q (goeMatrix r g))
    apply hfail
    refine ⟨by linarith,by linarith,?_⟩
    linarith
  calc
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real (E ∪ F) := measureReal_mono hs
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real E+
        (gaussianCoordinates (MatrixCoordinates ι)).real F := measureReal_union_le _ _
    _ ≤ _ := add_le_add (goe_norm_tail hj hε)
      (goe_diagonal_matrix_path_tail hj hA0 ha hA hsub herr)

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

lemma path_goodSet_failure {j A ε z : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (hε : 0 < ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) (hz : z ∈ Icc (0:ℝ) 1) :
    let r := j/(Fintype.card ι:ℝ)
    let q := r*∑ i, a i
    let R := 2*sqrt j+ε
    let lo := (1-sqrt j*A)^2/4
    let hi := 2+A*(R+j*A)
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet r (R+1) lo hi (pathDiagonal a z) (pathShift z q))ᶜ ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j))+
        Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) := by
  intro r q R lo hi
  apply le_trans ?_ (goe_path_spectral_tail hj hA0 hε.le ha hA hsub herr)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro g hg
  refine ⟨z,hz,?_⟩
  intro hg'
  apply hg
  rw [stabilityMatrix_path_rep a ha hz.1 q] at hg'
  simpa only [truncationGoodSet,Set.mem_ofPred_eq,lo,hi,R,r,div_div,
    show (2:ℝ)*2=4 by norm_num] using hg'

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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
lemma path_goodSet_exponential_oai {j A z : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) (2*sqrt j+1+1)
        ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  have hh := path_goodSet_failure hj hA0 (by norm_num : (0:ℝ)<1) ha hA hs herr hz
  dsimp only at hh
  apply hh.trans
  have h₁ := min_le_left (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))
  have h₂ := min_le_right (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))
  have he₁ : Real.exp (-(1:ℝ)^2*(Fintype.card ι:ℝ)/(π^2*j)) ≤
      Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply Real.exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    convert neg_le_neg (mul_le_mul_of_nonneg_right h₁ hn) using 1 <;> first | rfl | ring
  have he₂ : Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) ≤
      Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply Real.exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    convert neg_le_neg (mul_le_mul_of_nonneg_right h₂ hn) using 1 <;> first | rfl | ring
  linarith
end SKGap
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKGap.path_goodSet_exponential_oai.{u_1} := @OAI.SKGap.path_goodSet_exponential_oai.{u_1}
