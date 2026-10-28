-- Prove2me | solution 1 for OAI.SKGap.conditional_empirical_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:02.777877+00:00
-- url     : https://prove2.me/submissions/425a672d-d1c5-41d2-a098-d8a896f24151

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_compact_conditional_uniform_tail

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedMomentComparison
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma sum_abs_le_sqrt_card_l2 (d : ι → ℝ) :
    (∑ i, |d i|) ≤ √(Fintype.card ι:ℝ)*√(∑ i,d i^2) := by
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1:ℝ)) (fun i => |d i|)

theorem weighted_moment_comparison (a v y f : ι → ℝ) {H C D R : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (ha : ∀ i, |a i-v i| ≤ D)
    (hsmall : ∀ i, |y i| ≤ R → |f i| ≤ H)
    (hlarge : ∀ i, |f i| ≤ C*(1+y i^2)) :
    |∑ i,(a i-v i)*f i| ≤ H*√(Fintype.card ι:ℝ)*√(∑ i,(a i-v i)^2)+
      2*C*D*∑ i,if R < |y i| then y i^2 else 0 := by
  have hpoint (i : ι) : |(a i-v i)*f i| ≤ H*|a i-v i|+
      2*C*D*(if R < |y i| then y i^2 else 0) := by
    rw [abs_mul]
    by_cases hi : R < |y i|
    · rw [ite_eq_left hi]
      have hy : 1 ≤ y i^2 := by nlinarith [sq_abs (y i)]
      have hf : |f i| ≤ 2*C*y i^2 := (hlarge i).trans (by nlinarith)
      have hh := mul_le_mul (ha i) hf (abs_nonneg _) hD
      nlinarith [mul_nonneg hH (abs_nonneg (a i-v i))]
    · rw [ite_eq_right hi,mul_zero,add_zero]
      simpa only [mul_comm H] using mul_le_mul_of_nonneg_left (hsmall i (le_of_not_gt hi)) (abs_nonneg (a i-v i))
  calc
    _ ≤ ∑ i, |(a i-v i)*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,(H*|a i-v i|+2*C*D*(if R < |y i| then y i^2 else 0)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = H*(∑ i,|a i-v i|)+2*C*D*∑ i,if R < |y i| then y i^2 else 0 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ _ := by
      rw [mul_assoc H]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_l2 _) hH) le_rfl

theorem normalized_weighted_moment_comparison {n : ℕ} (hn : 0 < n)
    (a v y f : Fin n → ℝ) {H C D R ε ν : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 1 ≤ R)
    (hε : 0 ≤ ε) (ha : ∀ i, |a i-v i| ≤ D)
    (hsmall : ∀ i, |y i| ≤ R → |f i| ≤ H)
    (hlarge : ∀ i, |f i| ≤ C*(1+y i^2))
    (hclose : ∑ i,(a i-v i)^2 ≤ ε^2*(n:ℝ))
    (htail : (∑ i,if R < |y i| then y i^2 else 0) ≤ ν*(n:ℝ)) :
    |(∑ i,(a i-v i)*f i)/(n:ℝ)| ≤ H*ε+2*C*D*ν := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnorm : √(∑ i,(a i-v i)^2) ≤ ε*√(n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hnR.le]
  have h := weighted_moment_comparison a v y f hH hC hD hR ha hsmall hlarge
  simp only [Fintype.card_fin] at h
  have h' : |∑ i,(a i-v i)*f i| ≤ (H*ε+2*C*D*ν)*(n:ℝ) := by
    calc
      _ ≤ _ := h
      _ ≤ H*√(n:ℝ)*(ε*√(n:ℝ))+2*C*D*(ν*(n:ℝ)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hnorm (by positivity))
          (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = H*ε*(√(n:ℝ))^2+2*C*D*ν*(n:ℝ) := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]; ring
  rw [abs_div,abs_of_pos hnR]
  exact (div_le_iff₀ hnR).mpr h'
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedScalarMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory
open scoped BigOperators BoundedContinuousFunction

lemma continuous_weightedScalarMoment_integral (k l : Fin 3) :
    Continuous (fun P : ProbabilityMeasure ℝ => ∫ y, weightedScalarMoment k l y ∂P) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction _

end SKGap
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
-- module Solutions.OAIQ072_SK.SKGap_Localization_TruncationGoodSet
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
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open SKGap.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_transpose (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g)ᵀ = goeMatrix r g := by
  ext i k
  simp [goeMatrix,add_comm]

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

end Quadratic

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma operator_le_frobenius (M : Matrix ι ι ℝ) : opNorm M ≤ ‖M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hh := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit (fun i => x i))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hh
  exact hh

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramColumnBounds
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
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma frobenius_le_card_bound {M : Matrix κ κ ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hM : ∀ i k,|M i k| ≤ ε) : ‖M‖ ≤ (Fintype.card κ:ℝ)*ε := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ ∑ _i : κ,∑ _k : κ, ε^2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hε).mpr (hM i k)
    _ = _ := by simp; ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ConditionalGramTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixBilinear_eq_pair (M : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    matrixBilinear M x y=matrixPair M x.ofLp y.ofLp := by
  simp only [matrixBilinear,matrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1; ext i; congr 1; ext k; ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarParametersJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma momentCut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ momentCut n x :=
  le_min (Nat.cast_nonneg _) (sq_nonneg _)

lemma momentCut_tendsto (x : ℝ) : Tendsto (fun n => momentCut n x) atTop (𝓝 (x^2)) := by
  have he : ∀ᶠ n : ℕ in atTop, momentCut n x = x^2 := by
    obtain ⟨N,hN⟩ := exists_nat_ge (x^2)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact min_eq_right (hN.trans (by exact_mod_cast hn))
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma momentBall_iff (R : ℝ) (hR : 0 ≤ R) (P : ProbabilityMeasure ℝ) :
    P ∈ momentBall R ↔ ∀ n, (∫ x, momentCut n x ∂P) ≤ R := by
  constructor
  · intro h n
    apply (ENNReal.ofReal_le_ofReal_iff hR).mp
    rw [ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ)))
      (ae_of_all _ (momentCut_nonneg n))]
    exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))).trans h
  · intro h
    have ht : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (momentCut n x) ∂P) atTop
        (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P)) := by
      apply lintegral_tendsto_of_tendsto_of_monotone
      · intro n; exact (ENNReal.continuous_ofReal.comp (momentCut n).continuous).aemeasurable
      · exact ae_of_all _ (fun x a b hab => ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hab)))
      · exact ae_of_all _ (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (momentCut_tendsto x))
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ))) (ae_of_all _ (momentCut_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h n))

lemma isClosed_momentBall (R : ℝ) : IsClosed (momentBall R) := by
  have he : momentBall R = momentBall (max 0 R) := by simp only [momentBall, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0:ℝ≥0∞) ≤ ENNReal.ofReal R from bot_le)]
  rw [he]
  have hR : 0 ≤ max 0 R := le_max_left _ _
  have hes : momentBall (max 0 R) = ⋂ n, {P : ProbabilityMeasure ℝ | (∫ x, momentCut n x ∂P) ≤ max 0 R} := by
    ext P; simp only [mem_iInter, mem_ofPred_eq]; exact momentBall_iff _ hR P
  rw [hes]
  exact isClosed_iInter (fun n => isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const)

lemma momentBall_integrable {R : ℝ} {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    Integrable (fun x : ℝ => x^2) (P : Measure ℝ) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact lt_of_le_of_lt hP ENNReal.ofReal_lt_top

lemma momentBall_integral_le {R : ℝ} (hR : 0 ≤ R) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    (∫ x : ℝ, x^2 ∂P) ≤ R := by
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal (momentBall_integrable hP) (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact hP

lemma momentBall_tail {R K : ℝ} (hK : 0 < K) {P : ProbabilityMeasure ℝ}
    (hP : P ∈ momentBall R) :
    (P : Measure ℝ) (Metric.closedBall 0 K)ᶜ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) := by fun_prop
  calc
    _ ≤ (P : Measure ℝ) {x : ℝ | ENNReal.ofReal (K^2) ≤ ENNReal.ofReal (x^2)} := by
      apply measure_mono
      intro x hx
      have hx' : K < |x| := by simpa only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_abs x]
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P) / ENNReal.ofReal (K^2) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hK)) ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right hP _

lemma isTight_momentBall (R : ℝ) :
    IsTightMeasureSet {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ momentBall R} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hd : 0 < δ := ENNReal.ofReal_pos.mp hδ
  let K := max 0 R / δ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Metric.closedBall 0 K, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨P,hP,rfl⟩
  calc
    _ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := momentBall_tail hK hP
    _ ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hK)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (sq_pos_of_pos hK)]
      have hK1 : 1 ≤ K := by dsimp [K]; linarith [div_nonneg (le_max_left 0 R) hd.le]
      have he : δ * (K-1) = max 0 R := by dsimp [K]; field_simp; ring
      have hab : 0 ≤ (K-1)^2 := sq_nonneg _
      nlinarith [le_max_right 0 R, mul_nonneg hd.le hab]
    _ ≤ ε := hδε.le

lemma isCompact_momentBall (R : ℝ) : IsCompact (momentBall R) := by
  have h := isCompact_closure_of_isTightMeasureSet (isTight_momentBall R)
  simpa only [(isClosed_momentBall R).closure_eq] using h

lemma integrable_of_linear_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun x : ℝ => x^2) P) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C*(1+|x|)) : Integrable f P := by
  apply (((integrable_const (2:ℝ)).add hP).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (by change 1+|x| ≤ 2+x^2; linarith) hC))

lemma momentClip_error {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |x - max (-(n:ℝ)) (min (n:ℝ) x)| ≤ x^2/(n:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  by_cases hx : x ≤ (n:ℝ)
  · rw [min_eq_right hx]
    by_cases hx' : -(n:ℝ) ≤ x
    · rw [max_eq_right hx', sub_self, abs_zero, zero_mul]; positivity
    · rw [max_eq_left (le_of_not_ge hx'), abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (x+(n:ℝ))]
  · rw [min_eq_left (le_of_not_ge hx), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (x-(n:ℝ))]

lemma moment_integral_approx {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|))
    {n : ℕ} (hn : 0 < n) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    |(∫ x, f x ∂P) - (∫ x, momentClip hf n x ∂P)| ≤ 2*C^2*(1+R)/(n:ℝ) := by
  have hpi := momentBall_integrable hP
  have hfi := integrable_of_linear_bound hpi hf hC hb
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [← integral_sub hfi ((momentClip hf n).integrable (μ := (P : Measure ℝ))), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖f x - momentClip hf n x‖ ≤ (2*C^2/(n:ℝ))*(1+x^2) := by
    intro x
    rw [Real.norm_eq_abs]
    change |f x - max (-(n:ℝ)) (min (n:ℝ) (f x))| ≤ _
    apply (momentClip_error hn (f x)).trans
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn']
    have hsq : (f x)^2 ≤ (C*(1+|x|))^2 := by
      have h := mul_self_le_mul_self (abs_nonneg (f x)) (hb x)
      simpa only [← sq, sq_abs] using h
    have hs : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    calc
      _ ≤ (C*(1+|x|))^2 := hsq
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg C)]
  have he := norm_integral_le_of_norm_le
    (((integrable_const (1:ℝ)).add hpi).const_mul (2*C^2/(n:ℝ))) (ae_of_all _ hbound)
  calc
    _ ≤ ∫ x, (2*C^2/(n:ℝ))*(1+x^2) ∂P := he
    _ = (2*C^2/(n:ℝ))*(1+∫ x : ℝ, x^2 ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const 1) hpi]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2*C^2/(n:ℝ))*(1+R) := mul_le_mul_of_nonneg_left
      (by linarith [momentBall_integral_le hR hP]) (by positivity)
    _ = _ := by ring

lemma continuousOn_integral_of_linear_bound {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|)) :
    ContinuousOn (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) (momentBall R) := by
  have ht : TendstoUniformlyOn (fun n (P : ProbabilityMeasure ℝ) => ∫ x, momentClip hf n x ∂P)
      (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) atTop (momentBall R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (tendsto_const_div_atTop_nhds_zero_nat (2*C^2*(1+R))).eventually (gt_mem_nhds hε)
    filter_upwards [he, eventually_gt_atTop 0] with n hn hn0
    intro P hP
    rw [Real.dist_eq]
    exact (moment_integral_approx hR hC hf hb hn0 hP).trans_lt hn
  apply ht.continuousOn
  exact Frequently.of_forall (fun n => (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (momentClip hf n)).continuousOn)

end SKGap

namespace SKGap

lemma continuous_scalarM : Continuous scalarM := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup tanh continuous_tanh 1
    (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarQMoment : Continuous scalarQMoment := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => tanh x^2) (by fun_prop) 1
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarD (j : ℝ) : Continuous (scalarD j) :=
  (continuous_fst.comp continuous_snd).add (continuous_const.mul (continuous_scalarM.comp continuous_fst))

lemma continuous_scalarS (j : ℝ) : Continuous (scalarS j) :=
  ((continuous_fst.comp continuous_snd).add ((continuous_snd.comp continuous_snd).pow 2)).add
    (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))

lemma scalarQMoment_bounds (P : ProbabilityMeasure ℝ) : 0 ≤ scalarQMoment P ∧ scalarQMoment P ≤ 1 := by
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hi : Integrable (fun x : ℝ => tanh x^2) (P : Measure ℝ) := Integrable.of_bound
    (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le))
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => (tanh_sq_lt_one x).le)
  simpa only [scalarQMoment, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma scalarM_bounds (P : ProbabilityMeasure ℝ) : |scalarM P| ≤ 1 := by
  have h := norm_integral_le_of_norm_le (μ := (P : Measure ℝ)) (f := tanh) (integrable_const (1:ℝ))
    (ae_of_all _ (fun x : ℝ => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simpa only [scalarM, Real.norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma continuousOn_scalarA {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarA j) (scalarMomentDomain R) := by
  have hi := continuousOn_integral_of_linear_bound hR (C := 1) zero_le_one
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have hc : ContinuousOn (fun p : ScalarPoint => ∫ x, x*tanh x ∂p.1) (scalarMomentDomain R) :=
    hi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact hc.sub ((continuous_scalarD j).mul (continuous_scalarM.comp continuous_fst)).continuousOn

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarFixedPointJoined
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

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_zero : gaussianF 0 = 0 := by simp [gaussianF, gaussianAverage]

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_le_self {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ s := by
  have h := gaussianF_lipschitz.dist_le_mul s hs 0 (by simp)
  rw [gaussianF_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, abs_of_nonneg (gaussianF_nonneg hs), Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

end SKGap

namespace SKGap

lemma gaussianF_pos {s : ℝ} (hs : 0 < s) : 0 < gaussianF s := by
  rw [gaussianF_eq_square hs.le, gaussianAverage_eq_integral (by fun_prop) s hs.le]
  have hv : s.toNNReal ≠ 0 := by exact_mod_cast (show 0 < s.toNNReal from Real.toNNReal_pos.mpr hs).ne'
  have := nullSingletonClass_gaussianReal (μ := s) hv
  have hsupp : Function.support (fun y : ℝ => tanh y ^ 2) = ({0} : Set ℝ)ᶜ := by
    ext y
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff, ne_eq, sq_eq_zero_iff]
    have he : tanh y = 0 ↔ y = 0 := by
      simpa only [tanh_zero] using (show tanh y = tanh 0 ↔ y = 0 from tanh_injective.eq_iff)
    exact not_congr he
  rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg (tanh y)) integrable_tanh_sq,
    hsupp, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

lemma scalarFixedPoint_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    0 ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t = t+j*gaussianF (scalarFixedPoint j t) := by
  simp only [scalarFixedPoint, dite_eq_left (show 0 < j ∧ j < 1 ∧ 0 ≤ t from ⟨hj, hj1, ht⟩)]
  exact (exists_gaussian_fixed hj hj1 ht).choose_spec.1

lemma scalarFixedPoint_bounds {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    t ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  constructor
  · nlinarith [gaussianF_nonneg hs]
  · apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
    nlinarith [gaussianF_le_self hs]

lemma scalarFixedPoint_lipschitz {j t u : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    |scalarFixedPoint j t-scalarFixedPoint j u| ≤ 1/(1-j)*|t-u| := by
  obtain ⟨hst, het⟩ := scalarFixedPoint_spec hj hj1 ht
  obtain ⟨hsu, heu⟩ := scalarFixedPoint_spec hj hj1 hu
  have h := gaussianF_lipschitz.dist_le_mul _ hst _ hsu
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have htri : |scalarFixedPoint j t-scalarFixedPoint j u| ≤
      |t-u|+j*|gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u)| := by
    calc
      _ = |(t-u)+j*(gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u))| := by congr 1; linarith
      _ ≤ |t-u|+|j*(gaussianF (scalarFixedPoint j t)-gaussianF (scalarFixedPoint j u))| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_pos hj]
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
  nlinarith

lemma scalarQ_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQ j t = (∫ y, tanh y^2 ∂gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal) ∧
      scalarQ j t = (scalarFixedPoint j t-t)/j ∧ scalarQ j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  refine ⟨?_, ?_, ?_⟩
  · exact (gaussianF_eq_square hs).trans (gaussianAverage_eq_integral (by fun_prop) _ hs)
  · dsimp [scalarQ]; apply (eq_div_iff hj.ne').mpr; nlinarith
  · exact (gaussianF_le_self hs).trans (scalarFixedPoint_bounds hj hj1 ht).2

lemma scalar_fixed_pos {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    0 < scalarFixedPoint j t ∧ 0 < scalarQ j t := by
  have hs := ht.trans_le (scalarFixedPoint_bounds hj hj1 ht.le).1
  exact ⟨hs, gaussianF_pos hs⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianGramMomentsJoined
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

namespace SKGap

lemma spinVariance_nonneg (y : ℝ) : 0 ≤ scalarGramVariance y :=
  sub_nonneg.mpr (tanh_sq_lt_one y).le

lemma abs_spinVariance_le_one (y : ℝ) : |scalarGramVariance y| ≤ 1 := by
  rw [abs_of_nonneg (spinVariance_nonneg y)]
  unfold scalarGramVariance
  nlinarith [sq_nonneg (tanh y)]

lemma abs_spinMixed_le_one (y : ℝ) : |spinMixed y| ≤ 1 := by
  unfold spinMixed
  rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ 1*1 := mul_le_mul (tanh_sq_lt_one y).le (abs_spinVariance_le_one y) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma integrable_spinVariance {μ : Measure ℝ} [IsFiniteMeasure μ] : Integrable scalarGramVariance μ :=
  Integrable.of_bound (by unfold scalarGramVariance; fun_prop) 1
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))

lemma integrable_spinMixed {μ : Measure ℝ} [IsFiniteMeasure μ] : Integrable spinMixed μ :=
  Integrable.of_bound (by unfold spinMixed scalarGramVariance; fun_prop) 1
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinMixed_le_one y))

lemma gaussian_nishimori_variance (s : ℝ≥0) :
    (∫ y, oddVariance y ∂gaussianReal s s) = ∫ y, spinMixed y ∂gaussianReal s s := by
  by_cases hs : s = 0
  · subst s; simp [oddVariance,spinMixed,scalarGramVariance]
  have hi := (integrable_gaussian_iff hs).mp
    (integrable_oddVariance.sub (integrable_spinMixed (μ := gaussianReal s s)))
  let f : ℝ → ℝ := fun y => gaussianPDFReal s s y*(oddVariance y-spinMixed y)
  have hf : Integrable f := hi
  have hid (y : ℝ) : f y+f (-y) = 0 := by
    have hh := gaussianPDFReal_diagonal_symmetry hs y
    dsimp [f,oddVariance,spinMixed,scalarGramVariance]
    rw [tanh_neg,neg_sq]
    nlinarith [congrArg (fun x => tanh y*(1-tanh y^2)*x) hh]
  have hz : (∫ y, f y)+(∫ y, f (-y)) = 0 := by
    rw [← integral_add hf hf.comp_neg]
    simp only [hid,integral_zero]
  rw [integral_neg_eq_self] at hz
  have hsub : ∫ y, oddVariance y-spinMixed y ∂gaussianReal s s = 0 := by
    rw [integral_gaussianReal_eq_integral_smul hs]
    change (∫ y, f y) = 0
    linarith
  rw [integral_sub integrable_oddVariance integrable_spinMixed] at hsub
  exact sub_eq_zero.mp hsub

lemma hasDerivAt_spinVariance (y : ℝ) : HasDerivAt scalarGramVariance (-2*oddVariance y) y := by
  convert! (hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_tanh y).pow 2) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [oddVariance]; norm_num; ring

lemma hasDerivAt_oddVariance (y : ℝ) :
    HasDerivAt oddVariance (scalarGramVariance y-3*spinMixed y) y := by
  convert! (hasDerivAt_tanh y).mul (hasDerivAt_spinVariance y) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [spinMixed,scalarGramVariance,oddVariance]; ring

lemma integrable_center_spinVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)*scalarGramVariance y) (gaussianReal d s) := by
  have h := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul (f := scalarGramVariance)
    (by unfold scalarGramVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

lemma integrable_center_oddVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)*oddVariance y) (gaussianReal d s) := by
  have h := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul (f := oddVariance)
    (by unfold oddVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_oddVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

lemma integrable_center_sq_spinVariance (d : ℝ) (s : ℝ≥0) :
    Integrable (fun y => (y-d)^2*scalarGramVariance y) (gaussianReal d s) := by
  have hmem : MemLp (fun y : ℝ => y-d) 2 (gaussianReal d s) :=
    (IsGaussian.memLp_id (gaussianReal d s) 2 (by norm_num)).sub (memLp_const d)
  have h := hmem.integrable_sq.bdd_mul (f := scalarGramVariance)
    (by unfold scalarGramVariance; fun_prop) (c := 1)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using abs_spinVariance_le_one y))
  simpa only [mul_comm,Pi.sub_apply,id_eq] using h

theorem gaussian_weighted_gram_moments {s : ℝ≥0} (hs : 0 < s) :
    (∫ y, (y-(s:ℝ))*scalarGramVariance y ∂gaussianReal s s) =
      -2*(s:ℝ)*(∫ y, spinMixed y ∂gaussianReal s s) ∧
    (∫ y, (y-(s:ℝ))*oddVariance y ∂gaussianReal s s) =
      (s:ℝ)*((∫ y, scalarGramVariance y ∂gaussianReal s s)-3*(∫ y, spinMixed y ∂gaussianReal s s)) ∧
    (∫ y, (y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s) =
      (s:ℝ)*(∫ y, scalarGramVariance y ∂gaussianReal s s)+
      (s:ℝ)^2*(-2*(∫ y, scalarGramVariance y ∂gaussianReal s s)+6*(∫ y, spinMixed y ∂gaussianReal s s)) := by
  have h1 := gaussian_integration_by_parts hs.ne' hasDerivAt_spinVariance
    integrable_spinVariance (integrable_oddVariance.const_mul (-2))
    (integrable_center_spinVariance s s)
  rw [integral_const_mul,gaussian_nishimori_variance] at h1
  have h2 := gaussian_integration_by_parts hs.ne' hasDerivAt_oddVariance
    integrable_oddVariance (integrable_spinVariance.sub (integrable_spinMixed.const_mul 3))
    (integrable_center_oddVariance s s)
  rw [integral_sub integrable_spinVariance (integrable_spinMixed.const_mul 3),integral_const_mul] at h2
  have hder (y : ℝ) : HasDerivAt (fun y => (y-(s:ℝ))*scalarGramVariance y)
      (scalarGramVariance y-2*((y-(s:ℝ))*oddVariance y)) y := by
    convert! ((hasDerivAt_id y).sub_const (s:ℝ)).mul (hasDerivAt_spinVariance y) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq,one_mul]; ring
  have h3 := gaussian_integration_by_parts hs.ne' hder (integrable_center_spinVariance s s)
    (integrable_spinVariance.sub ((integrable_center_oddVariance s s).const_mul 2))
    ((integrable_center_sq_spinVariance s s).congr (ae_of_all _ (fun y => by ring)))
  have h3' : (∫ y, (y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s) =
      (s:ℝ)*((∫ y, scalarGramVariance y ∂gaussianReal s s)-2*(∫ y, (y-(s:ℝ))*oddVariance y ∂gaussianReal s s)) := by
    convert h3 using 1
    · congr 1; funext y; ring
    · rw [integral_sub integrable_spinVariance ((integrable_center_oddVariance s s).const_mul 2),integral_const_mul]
  refine ⟨?_,h2,?_⟩
  · linarith [h1]
  · rw [h3',h2]; ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

theorem gaussian_weighted_gram_matrix {s : ℝ≥0} (hs : 0 < s) :
    (fun i k : Fin 3 => ∫ y, scalarGramVariance y*scalarGramVector s y i*scalarGramVector s y k
      ∂gaussianReal s s)=
      limitingGram (∫ y,scalarGramVariance y ∂gaussianReal s s)
        (∫ y,spinMixed y ∂gaussianReal s s) s := by
  have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨h1,h2,h3⟩ := gaussian_weighted_gram_moments hs
  have h01 : (∫ y,scalarGramVariance y*tanh y ∂gaussianReal s s)=∫ y,spinMixed y ∂gaussianReal s s := by
    convert gaussian_nishimori_variance s using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext y; unfold oddVariance scalarGramVariance; ring
  have h02 : (∫ y,scalarGramVariance y*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      -2*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))*scalarGramVariance y ∂gaussianReal s s)/(s:ℝ) := by
        rw [← integral_div]; congr 1; funext y; ring
      _ = _ := by rw [h1]; field_simp
  have h11 : (∫ y,scalarGramVariance y*tanh y*tanh y ∂gaussianReal s s)=
      ∫ y,spinMixed y ∂gaussianReal s s := by
    congr 1; funext y; unfold spinMixed; ring
  have h12 : (∫ y,scalarGramVariance y*tanh y*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      (∫ y,scalarGramVariance y ∂gaussianReal s s)-3*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))*oddVariance y ∂gaussianReal s s)/(s:ℝ) := by
        rw [← integral_div]; congr 1; funext y; unfold oddVariance scalarGramVariance; ring
      _ = _ := by rw [h2]; field_simp
  have h22 : (∫ y,scalarGramVariance y*((y-(s:ℝ))/(s:ℝ))*((y-(s:ℝ))/(s:ℝ)) ∂gaussianReal s s)=
      (∫ y,scalarGramVariance y ∂gaussianReal s s)/(s:ℝ)-
        2*(∫ y,scalarGramVariance y ∂gaussianReal s s)+6*(∫ y,spinMixed y ∂gaussianReal s s) := by
    calc
      _ = (∫ y,(y-(s:ℝ))^2*scalarGramVariance y ∂gaussianReal s s)/(s:ℝ)^2 := by
        rw [← integral_div]; congr 1; funext y; ring
      _ = _ := by rw [h3]; field_simp; ring
  have hsym (i k : Fin 3) :
      (∫ y,scalarGramVariance y*scalarGramVector s y i*scalarGramVector s y k ∂gaussianReal s s)=
        ∫ y,scalarGramVariance y*scalarGramVector s y k*scalarGramVector s y i ∂gaussianReal s s := by
    congr 1; funext y; ring
  ext i k
  fin_cases i <;> fin_cases k
  · simp [scalarGramVector,limitingGram]
  · simpa [scalarGramVector,limitingGram] using h01
  · simpa [scalarGramVector,limitingGram] using h02
  · simpa [scalarGramVector,limitingGram] using (hsym 1 0).trans (by simpa [scalarGramVector] using h01)
  · simpa [scalarGramVector,limitingGram] using h11
  · simpa [scalarGramVector,limitingGram] using h12
  · simpa [scalarGramVector,limitingGram] using (hsym 2 0).trans (by simpa [scalarGramVector] using h02)
  · simpa [scalarGramVector,limitingGram] using (hsym 2 1).trans (by simpa [scalarGramVector] using h12)
  · simpa [scalarGramVector,limitingGram] using h22

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma card_mul_integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (Fintype.card ι : ℝ)*(∫ x, f x ∂empiricalLaw y) = ∑ i, f (y i) := by
  rw [integral_empiricalLaw, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne'), one_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ScalarMomentGram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarMomentGram_integral (P : ProbabilityMeasure ℝ) (d s : ℝ) :
    scalarMomentGram P d s = fun i k => ∫ y,
      (1-tanh y^2)*gramCoordinates d s y i*gramCoordinates d s y k ∂P := by
  have hi (k l : Fin 3) := (weightedScalarMoment k l).integrable (μ := (P : Measure ℝ))
  have h00 : (∫ y,(1-tanh y^2) ∂P)=∫ y,weightedScalarMoment 0 0 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]
  have h01 : (∫ y,(1-tanh y^2)*tanh y ∂P)=∫ y,weightedScalarMoment 0 1 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]; ring
  have h02 : (∫ y,(1-tanh y^2)*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 1 0 y ∂P)-d*(∫ y,weightedScalarMoment 0 0 y ∂P))/s := by
    calc
      _ = ∫ y,(weightedScalarMoment 1 0 y-d*weightedScalarMoment 0 0 y)/s ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by rw [integral_div,integral_sub (hi 1 0) ((hi 0 0).const_mul d),integral_const_mul]
  have h11 : (∫ y,(1-tanh y^2)*tanh y*tanh y ∂P)=∫ y,weightedScalarMoment 0 2 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]; ring
  have h12 : (∫ y,(1-tanh y^2)*tanh y*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 1 1 y ∂P)-d*(∫ y,weightedScalarMoment 0 1 y ∂P))/s := by
    calc
      _ = ∫ y,(weightedScalarMoment 1 1 y-d*weightedScalarMoment 0 1 y)/s ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by rw [integral_div,integral_sub (hi 1 1) ((hi 0 1).const_mul d),integral_const_mul]
  have h22 : (∫ y,(1-tanh y^2)*((y-d)/s)*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 2 0 y ∂P)-2*d*(∫ y,weightedScalarMoment 1 0 y ∂P)+
        d^2*(∫ y,weightedScalarMoment 0 0 y ∂P))/s^2 := by
    calc
      _ = ∫ y,(weightedScalarMoment 2 0 y-2*d*weightedScalarMoment 1 0 y+
          d^2*weightedScalarMoment 0 0 y)/s^2 ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by
        rw [integral_div,integral_add (show Integrable (fun y => weightedScalarMoment 2 0 y-2*d*weightedScalarMoment 1 0 y) (P : Measure ℝ) from
          (hi 2 0).sub ((hi 1 0).const_mul (2*d))) ((hi 0 0).const_mul (d^2)),
          integral_sub (hi 2 0) ((hi 1 0).const_mul (2*d))]
        simp only [integral_const_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [scalarMomentGram,gramCoordinates]
  all_goals first | exact h00.symm | exact h01.symm | exact h02.symm |
    exact h11.symm | exact h12.symm | exact h22.symm |
    (convert h12.symm using 1; congr 1; funext y; ring)

lemma continuousAt_scalarMomentGram {p : ProbabilityMeasure ℝ × (ℝ × ℝ)} (hs : p.2.2 ≠ 0) :
    ContinuousAt (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => scalarMomentGram p.1 p.2.1 p.2.2) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  have hm (i k : Fin 3) : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) =>
      ∫ y,weightedScalarMoment i k y ∂p.1) :=
    (continuous_weightedScalarMoment_integral i k).comp continuous_fst
  have hd : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => p.2.1) := continuous_fst.comp continuous_snd
  have hss : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.comp continuous_snd
  fin_cases i <;> fin_cases k <;>
    simp only [scalarMomentGram, Matrix.of_apply, Matrix.cons_val,Fin.isValue,Fin.reduceFinMk]
  all_goals first | exact (hm _ _).continuousAt |
    exact ((hm _ _).continuousAt.sub (hd.continuousAt.mul (hm _ _).continuousAt)).div hss.continuousAt hs |
    exact (((hm _ _).continuousAt.sub
      ((continuousAt_const.mul hd.continuousAt).mul (hm _ _).continuousAt)).add
      ((hd.continuousAt.pow 2).mul (hm _ _).continuousAt)).div
      (hss.continuousAt.pow 2) (pow_ne_zero _ hs)

lemma scalarMomentGram_empirical {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d s : ℝ) :
    scalarMomentGram (empiricalLaw y) d s = fun i k =>
      (n:ℝ)⁻¹*∑ l,(1-tanh (y l)^2)*gramCoordinates d s (y l) i*gramCoordinates d s (y l) k := by
  rw [scalarMomentGram_integral]
  ext i k
  simp only [integral_empiricalLaw,Fintype.card_fin]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalRankAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*}

lemma conditionalCoefficient_hermitian (j cM cG cN : ℝ) :
    (conditionalCoefficient j cM cG cN).IsHermitian := by
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;> simp [conditionalCoefficient,Matrix.conjTranspose_apply]
    | inr k => simp [conditionalCoefficient,Matrix.conjTranspose_apply]
  | inr i => cases k <;> simp [conditionalCoefficient,Matrix.conjTranspose_apply]

lemma conditional_rank_expansion (X M G N : ι → ℝ) (j cM cG cN : ℝ) :
    conditionalColumns X M G N*conditionalCoefficient j cM cG cN*
      (conditionalColumns X M G N)ᵀ =
      j • vecMulVec X X+cM • vecMulVec M M+
      cG • (vecMulVec M G+vecMulVec G M)+cN • (vecMulVec M N+vecMulVec N M) := by
  ext i k
  simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,
    conditionalColumns,conditionalCoefficient,conditionalCoupling,vecMulVec_apply]
  ring

theorem conditional_rank_change_basis (X U Z V : ι → ℝ) (j cU cZ cV : ℝ)
    {q s B : ℝ} (hq : 0 < q) (hs : 0 < s) (hB : 0 < B) :
    let Q := conditionalColumns X (√q • U) ((√s)⁻¹ • Z) ((√B)⁻¹ • (V-B • U))
    Q*conditionalCoefficient j ((cU+2*B*cV)/q) (cZ*√s/√q) (cV*√B/√q)*Qᵀ =
      j • vecMulVec X X+cU • vecMulVec U U+
      cZ • (vecMulVec U Z+vecMulVec Z U)+cV • (vecMulVec U V+vecMulVec V U) := by
  dsimp only
  rw [conditional_rank_expansion]
  have hq0 : √q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hs0 : √s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hB0 : √B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  ext i k
  simp only [Matrix.add_apply,Matrix.smul_apply,vecMulVec_apply,Pi.smul_apply,Pi.sub_apply,
    smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hq.le]; ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EqualityCurve
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal

lemma scalarBMoment_integral (P : ProbabilityMeasure ℝ) :
    scalarBMoment P=∫ y,scalarGramVariance y ∂P := by
  unfold scalarBMoment scalarQMoment scalarGramVariance
  rw [integral_sub (integrable_const 1) integrable_tanh_sq]
  simp

lemma scalarEMoment_integral (P : ProbabilityMeasure ℝ) :
    scalarEMoment P=∫ y,spinMixed y ∂P := by
  unfold scalarEMoment
  congr 1
  funext y
  simp [weightedScalarMoment,spinMixed,scalarGramVariance]

lemma scalarBMoment_pos (P : ProbabilityMeasure ℝ) : 0 < scalarBMoment P := by
  rw [scalarBMoment_integral,integral_pos_iff_support_of_nonneg spinVariance_nonneg integrable_spinVariance]
  have he : Function.support scalarGramVariance=univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (sub_pos.mpr (tanh_sq_lt_one y))
  rw [he,measure_univ]
  exact zero_lt_one

lemma scalarBMoment_le_one (P : ProbabilityMeasure ℝ) : scalarBMoment P ≤ 1 := by
  have h := (scalarQMoment_bounds P).1
  unfold scalarBMoment
  linarith

lemma scalarEMoment_nonneg (P : ProbabilityMeasure ℝ) : 0 ≤ scalarEMoment P := by
  rw [scalarEMoment_integral]
  exact integral_nonneg (fun y=>mul_nonneg (sq_nonneg _) (spinVariance_nonneg _))

lemma continuous_scalarBMoment : Continuous scalarBMoment := continuous_const.sub continuous_scalarQMoment
lemma continuous_scalarEMoment : Continuous scalarEMoment := continuous_weightedScalarMoment_integral 0 2

lemma continuous_scalarFixedPoint_nonneg {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    Continuous (fun t : Ici (0:ℝ) => scalarFixedPoint j t) := by
  have hjgap : 0 < 1-j := sub_pos.mpr hj1
  have hL : LipschitzWith (⟨1/(1-j),by positivity⟩ : ℝ≥0)
      (fun t : Ici (0:ℝ) => scalarFixedPoint j t) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    change |scalarFixedPoint j t-scalarFixedPoint j u| ≤ (1/(1-j))*|((t:ℝ)-(u:ℝ))|
    exact scalarFixedPoint_lipschitz hj hj1 t.2 u.2
  exact hL.continuous

lemma continuous_scalarCurve_nonneg {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    Continuous (fun t : Ici (0:ℝ) => scalarCurve j t) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hc := (continuous_gaussianAverage f.continuous (C := ‖f‖) (fun y=>f.norm_coe_le_norm y)).comp
    ((continuous_scalarFixedPoint_nonneg hj hj1).prodMk (continuous_scalarFixedPoint_nonneg hj hj1))
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact (gaussianAverage_eq_integral f.continuous _ (scalarFixedPoint_spec hj hj1 t.2).1).symm

lemma scalarQMoment_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQMoment (scalarCurve j t)=scalarQ j t := (scalarQ_spec hj hj1 ht).1.symm

lemma scalarM_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarM (scalarCurve j t)=scalarQ j t := by
  have hs := (scalarFixedPoint_spec hj hj1 ht).1
  have h := gaussian_nishimori (scalarFixedPoint j t).toNNReal
  simp only [Real.coe_toNNReal _ hs] at h
  exact h.trans (scalarQMoment_curve hj hj1 ht)

lemma scalarD_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarD j (scalarCurve j t,t,0)=scalarFixedPoint j t := by
  rw [scalarD,scalarM_curve hj hj1 ht]
  exact (scalarFixedPoint_spec hj hj1 ht).2.symm

lemma scalarS_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarS j (scalarCurve j t,t,0)=scalarFixedPoint j t := by
  rw [scalarS,scalarQMoment_curve hj hj1 ht]
  simpa only [zero_pow (by decide : 2 ≠ 0),add_zero,scalarQ] using (scalarFixedPoint_spec hj hj1 ht).2.symm

lemma scalarA_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    scalarA j (scalarCurve j t,t,0)=scalarFixedPoint j t*scalarBMoment (scalarCurve j t) := by
  let s := scalarFixedPoint j t
  have hs : 0 < s := (scalar_fixed_pos hj hj1 ht).1
  have hn : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have hi : Integrable (fun y : ℝ => (y-s)*tanh y) (gaussianReal s s.toNNReal) :=
    ((IsGaussian.integrable_id (μ := gaussianReal s s.toNNReal)).sub (integrable_const s)).mul_bdd
      (c := 1) continuous_tanh.aestronglyMeasurable (ae_of_all _ (fun y=>by simpa using (abs_tanh_lt_one y).le))
  have hyt : Integrable (fun y : ℝ => y*tanh y) (gaussianReal s s.toNNReal) :=
    (IsGaussian.integrable_id (μ := gaussianReal s s.toNNReal)).mul_bdd
      (c := 1) continuous_tanh.aestronglyMeasurable (ae_of_all _ (fun y=>by simpa using (abs_tanh_lt_one y).le))
  have hibp := gaussian_integration_by_parts hn hasDerivAt_tanh integrable_tanh
    integrable_spinVariance hi
  rw [Real.coe_toNNReal _ hs.le] at hibp
  unfold scalarA
  rw [scalarD_curve hj hj1 ht.le,scalarBMoment_integral]
  change (∫ y,y*tanh y ∂gaussianReal s s.toNNReal)-s*(∫ y,tanh y ∂gaussianReal s s.toNNReal)=s*(∫ y,1-tanh y^2 ∂gaussianReal s s.toNNReal)
  rw [← integral_const_mul,← integral_sub hyt (integrable_tanh.const_mul s)]
  convert hibp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  ring

lemma scalarMomentGram_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    scalarMomentGram (scalarCurve j t) (scalarFixedPoint j t) (scalarFixedPoint j t)=
      limitingGram (scalarBMoment (scalarCurve j t)) (scalarEMoment (scalarCurve j t))
        (scalarFixedPoint j t) := by
  have hs := (scalar_fixed_pos hj hj1 ht).1
  have h := gaussian_weighted_gram_matrix (s := (scalarFixedPoint j t).toNNReal)
    (by exact_mod_cast (Real.toNNReal_pos.mpr hs))
  rw [scalarMomentGram_integral,scalarBMoment_integral,scalarEMoment_integral]
  ext i k
  simpa only [Real.coe_toNNReal _ hs.le,scalarCurve,scalarGramVector,gramCoordinates,
    scalarGramVariance,ProbabilityMeasure.coe_mk] using congrFun (congrFun h i) k
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEBlockExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma symmetric_dot_mulVec (W : Matrix ι ι ℝ) (hW : Wᵀ=W) (u : ι → ℝ) (k : ι) :
    u⬝ᵥ(W*ᵥPi.single k 1)=(W*ᵥu) k := by
  rw [Matrix.mulVec_single_one]
  change (∑ i,u i*W i k)=∑ i,W k i*u i
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun M : Matrix ι ι ℝ => M k i) hW
  simpa only [Matrix.transpose_apply,mul_comm] using congrArg (fun a => a*u i) h

theorem goeBlockResidual_expand (r κ ell : ℝ) (u : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) :
    goeBlockResidual r κ ell u g=goeMatrix r g+
      (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u := by
  ext i k
  simp only [goeBlockResidual,goeBilinear,unitRow,Matrix.mulVec_add,Matrix.mulVec_smul,
    dotProduct_add,add_dotProduct,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    single_one_dotProduct,Matrix.mulVec_single_one,Matrix.add_apply,
    Matrix.smul_apply,vecMulVec_apply]
  have h := symmetric_dot_mulVec (goeMatrix r g) (goeMatrix_transpose _ _) u k
  simp only [Matrix.mulVec_single_one] at h
  rw [h]
  change _+_ = _
  dsimp only [Matrix.col, Matrix.transpose_apply]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalModelAlgebra
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

lemma conditionalCoefficient_add_scalar (j cM cG cN z w : ℝ) :
    conditionalCoefficient j cM cG cN+
      z • conditionalCoefficient 0 w 0 0=
      conditionalCoefficient j (cM+z*w) cG cN := by
  ext i k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp [conditionalCoefficient]
    | inr k => fin_cases i <;> simp [conditionalCoefficient,conditionalCoupling]
  | inr i => cases k with
    | inl k => fin_cases k <;> simp [conditionalCoefficient,conditionalCoupling]
    | inr k => simp [conditionalCoefficient]

lemma conditionalMeanCoefficient_equality {j q s b κ : ℝ}
    (hs : 0 < s) (hq : 0 < q) (hj : 0 ≤ j) :
    conditionalMeanCoefficient j q s (s+j*q) (s*b) (j*b) (j*b) κ=
      conditionalCoefficient j ((2*j*q+2*(j*b)*(κ-1))/q) j ((κ-1)*sqrt (j*b)/sqrt q) := by
  have hS : s+j*q ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq.le))
  unfold conditionalMeanCoefficient
  congr 1
  field_simp
  ring

theorem conditional_hessian_rank_form (r j a B κ ell : ℝ)
    {q s S BA : ℝ} (hq : 0 < q) (hs : 0 < s) (hBA : 0 < BA)
    (X u Z : ι → ℝ) (D : Matrix ι ι ℝ) (g : MatrixCoordinates ι → ℝ) :
    let W := goeMatrix r g
    let Q := conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
      (residualGramVector BA W u)
    1+D*(B • (1 : Matrix ι ι ℝ)-conditionalBlockMatrix r j q s S a B κ ell u Z g-
      j • vecMulVec X X-(2*j*q) • vecMulVec u u)*D=
      (1-D*(W-BA • (1 : Matrix ι ι ℝ))*D)-
      D*Q*(conditionalMeanCoefficient j q s S a B BA κ+
        goeBilinear r u u g • conditionalScalarCoefficient q κ ell)*Qᵀ*D+
      (B-BA) • (D*D) := by
  dsimp only
  have hroot : sqrt (q/s)*sqrt s/sqrt q=1 := by
    rw [Real.sqrt_div hq.le]
    field_simp
  have hz : j*sqrt (q/s)*sqrt s/sqrt q=j := by
    calc
      _ = j*(sqrt (q/s)*sqrt s/sqrt q) := by ring
      _ = _ := by rw [hroot,mul_one]
  have hrank := conditional_rank_change_basis X u Z (goeMatrix r g*ᵥu) j
    (2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g)
    (j*sqrt (q/s)) (κ-1) hq hs hBA
  dsimp only at hrank
  rw [hz] at hrank
  have hc : conditionalMeanCoefficient j q s S a B BA κ+
      goeBilinear r u u g • conditionalScalarCoefficient q κ ell=
      conditionalCoefficient j
        ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g+2*BA*(κ-1))/q)
        j ((κ-1)*sqrt BA/sqrt q) := by
    unfold conditionalMeanCoefficient conditionalScalarCoefficient
    rw [conditionalCoefficient_add_scalar]
    congr 1
    ring
  rw [hc]
  change _ = (1-D*(goeMatrix r g-BA • (1 : Matrix ι ι ℝ))*D)-D*_*_*_*D+_
  have hrank' := congrArg (fun M => D*M*D) hrank
  simp only [Matrix.mul_assoc] at hrank'
  simp only [residualGramVector] at *
  rw [show D*conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
        ((sqrt BA)⁻¹ • (goeMatrix r g*ᵥu-BA • u))*
        conditionalCoefficient j
          ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g+2*BA*(κ-1))/q)
          j ((κ-1)*sqrt BA/sqrt q)*
        (conditionalColumns X (sqrt q • u) ((sqrt s)⁻¹ • Z)
          ((sqrt BA)⁻¹ • (goeMatrix r g*ᵥu-BA • u)))ᵀ*D=
        D*(j • vecMulVec X X+
          (2*j*q-2*j*a/s+2*j*(a+B*q)/S+(ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
          (j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)+
          (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u))*D by
          simpa only [Matrix.mul_assoc] using hrank']
  unfold conditionalBlockMatrix
  rw [goeBlockResidual_expand]
  have he : vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u=
      (j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)-(2*j*a/s) • vecMulVec u u := by
    ext i k
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,vecMulVec_apply,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hcombine : goeMatrix r g+
      (κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
      vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u=
      goeMatrix r g+(κ-1) • (vecMulVec u (goeMatrix r g*ᵥu)+vecMulVec (goeMatrix r g*ᵥu) u)+
      ((ell-2*κ+1)*goeBilinear r u u g) • vecMulVec u u+
      ((j*sqrt (q/s)) • (vecMulVec u Z+vecMulVec Z u)-(2*j*a/s) • vecMulVec u u) := by
    rw [← he]
    abel
  rw [hcombine]
  simp only [Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,sub_smul,add_smul]
  abel
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

lemma conditionalKappa_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    conditionalKappa j (scalarCurve j t,t,0)=curveKappa j t := by
  simp only [conditionalKappa,curveKappa,scalarS_curve hj hj1 ht,zero_pow (by decide : 2 ≠ 0),add_zero]

lemma curveKappa_sq {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    curveKappa j t^2=1-j*scalarQ j t/scalarFixedPoint j t := by
  have hs := (scalar_fixed_pos hj hj1 ht).1
  unfold curveKappa
  rw [Real.sq_sqrt (div_nonneg ht.le hs.le)]
  have he := (scalarFixedPoint_spec hj hj1 ht.le).2
  change scalarFixedPoint j t=t+j*scalarQ j t at he
  field_simp
  linarith

lemma conditionalMeanData_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    conditionalMeanData j (scalarCurve j t,t,0) 0=curveCoefficient j t := by
  unfold conditionalMeanData curveCoefficient
  rw [scalarQMoment_curve hj hj1 ht.le,scalarS_curve hj hj1 ht.le,
    scalarA_curve hj hj1 ht,conditionalKappa_curve hj hj1 ht.le,add_zero]
  exact conditionalMeanCoefficient_equality (scalar_fixed_pos hj hj1 ht).1
    (scalar_fixed_pos hj hj1 ht).2 hj.le

lemma continuousAt_conditionalCoefficient {X : Type*} [TopologicalSpace X]
    {j a b c : X → ℝ} {x : X} (hj : ContinuousAt j x) (ha : ContinuousAt a x)
    (hb : ContinuousAt b x) (hc : ContinuousAt c x) :
    ContinuousAt (fun x=>conditionalCoefficient (j x) (a x) (b x) (c x)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  cases i with
  | inl i => cases k with
    | inl k => fin_cases i <;> fin_cases k <;>
        simp only [conditionalCoefficient,fromBlocks_apply₁₁,Matrix.of_apply,Matrix.cons_val,Fin.reduceFinMk] <;> first | exact hj | exact ha | exact hb | exact continuousAt_const
    | inr k => fin_cases i <;> simp [conditionalCoefficient,conditionalCoupling] <;> first | exact hc | exact continuousAt_const
  | inr i => cases k with
    | inl k => fin_cases k <;> simp [conditionalCoefficient,conditionalCoupling] <;> first | exact hc | exact continuousAt_const
    | inr k => simp [conditionalCoefficient]; exact continuousAt_const

lemma continuousAt_conditionalData {X : Type*} [TopologicalSpace X]
    {R j : ℝ} (hR : 0 ≤ R) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) (r : X → ℝ) (hr : Continuous r)
    {x : X} (hq : 0 < scalarQMoment (f x).1) (hs : 0 < scalarS j (f x))
    (hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1) :
    ContinuousAt (fun x=>conditionalMeanData j (f x) (r x)) x ∧
    ContinuousAt (fun x=>conditionalScalarData j (f x)) x := by
  have hcq : Continuous (fun x=>scalarQMoment (f x).1) := continuous_scalarQMoment.comp (continuous_fst.comp hf)
  have hcs : Continuous (fun x=>scalarS j (f x)) := (continuous_scalarS j).comp hf
  have hcS : Continuous (fun x=>scalarS j (f x)+j*scalarQMoment (f x).1) := hcs.add (continuous_const.mul hcq)
  have hca : Continuous (fun x=>scalarA j (f x)) := (continuousOn_scalarA hR j).comp_continuous hf hdom
  have hcb : Continuous (fun x=>j*scalarBMoment (f x).1) := continuous_const.mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))
  have hcn : Continuous (fun x=>(f x).2.1+(f x).2.2^2) := by fun_prop
  have hk : ContinuousAt (fun x=>conditionalKappa j (f x)) x := (hcn.continuousAt.div hcs.continuousAt hs.ne').sqrt
  have hl : ContinuousAt (fun x=>conditionalEll j (f x)) x := (hcn.continuousAt.div hcS.continuousAt hS.ne').sqrt
  have hq' := hcq.continuousAt (x := x)
  have hs' := hcs.continuousAt (x := x)
  have hS' := hcS.continuousAt (x := x)
  have ha' := hca.continuousAt (x := x)
  have hb' := hcb.continuousAt (x := x)
  have hba := hb'.add hr.continuousAt
  have hM : ContinuousAt (fun x =>
      (2*j*scalarQMoment (f x).1-2*j*scalarA j (f x)/scalarS j (f x)+
        2*j*(scalarA j (f x)+j*scalarBMoment (f x).1*scalarQMoment (f x).1)/(scalarS j (f x)+j*scalarQMoment (f x).1)+
        2*(j*scalarBMoment (f x).1+r x)*(conditionalKappa j (f x)-1))/scalarQMoment (f x).1) x :=
    ((((continuousAt_const.mul hq').sub ((continuousAt_const.mul ha').div hs' hs.ne')).add
      ((continuousAt_const.mul (ha'.add (hb'.mul hq'))).div hS' hS.ne')).add
      ((continuousAt_const.mul hba).mul (hk.sub continuousAt_const))).div hq' hq.ne'
  have hN : ContinuousAt (fun x => (conditionalKappa j (f x)-1)*sqrt (j*scalarBMoment (f x).1+r x)/sqrt (scalarQMoment (f x).1)) x :=
    ((hk.sub continuousAt_const).mul hba.sqrt).div hq'.sqrt (sqrt_pos.mpr hq).ne'
  constructor
  · exact continuousAt_conditionalCoefficient continuousAt_const hM continuousAt_const hN
  · have hM' : ContinuousAt (fun x => (conditionalEll j (f x)-2*conditionalKappa j (f x)+1)/scalarQMoment (f x).1) x :=
      ((hl.sub (continuousAt_const.mul hk)).add continuousAt_const).div hq' hq.ne'
    exact continuousAt_conditionalCoefficient continuousAt_const hM' continuousAt_const continuousAt_const

lemma continuous_curve_statistics {j t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht0 : 0 < t0) :
    Continuous (fun t : Icc t0 T=>scalarFixedPoint j t) ∧
    Continuous (fun t : Icc t0 T=>scalarQ j t) ∧
    Continuous (fun t : Icc t0 T=>scalarBMoment (scalarCurve j t)) ∧
    Continuous (fun t : Icc t0 T=>scalarEMoment (scalarCurve j t)) ∧
    Continuous (fun t : Icc t0 T=>curveKappa j t) ∧
    Continuous (fun t : Icc t0 T=>curveCoefficient j t) := by
  let inc : Icc t0 T → Ici (0:ℝ) := fun t=>⟨t,ht0.le.trans t.2.1⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  have hs := (continuous_scalarFixedPoint_nonneg hj hj1).comp hi
  have hcurve := (continuous_scalarCurve_nonneg hj hj1).comp hi
  have hq : Continuous (fun t : Icc t0 T=>scalarQ j t) := by
    convert continuous_scalarQMoment.comp hcurve using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    exact (scalarQMoment_curve hj hj1 (ht0.le.trans t.2.1)).symm
  have hb := continuous_scalarBMoment.comp hcurve
  have he := continuous_scalarEMoment.comp hcurve
  have hk : Continuous (fun t : Icc t0 T=>curveKappa j t) :=
    (continuous_subtype_val.div hs (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).1.ne')).sqrt
  refine ⟨hs,hq,hb,he,hk,?_⟩
  apply continuous_iff_continuousAt.mpr
  intro t
  have hqt : 0 < scalarQ j (t:ℝ) := (scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).2
  have hq' := hq.continuousAt (x := t)
  have hb' := hb.continuousAt (x := t)
  have hk' := hk.continuousAt (x := t)
  have hM : ContinuousAt (fun t : Icc t0 T =>
      (2*j*scalarQ j t+2*(j*scalarBMoment (scalarCurve j t))*(curveKappa j t-1))/scalarQ j t) t :=
    ((continuousAt_const.mul hq').add
      ((continuousAt_const.mul (continuousAt_const.mul hb')).mul (hk'.sub continuousAt_const))).div hq' hqt.ne'
  have hN : ContinuousAt (fun t : Icc t0 T => (curveKappa j t-1)*sqrt (j*scalarBMoment (scalarCurve j t))/sqrt (scalarQ j t)) t :=
    ((hk'.sub continuousAt_const).mul (continuousAt_const.mul hb').sqrt).div hq'.sqrt (sqrt_pos.mpr hqt).ne'
  exact continuousAt_conditionalCoefficient continuousAt_const hM continuousAt_const hN
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CompactTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Set Filter Topology
lemma compact_perturbation_tube_norm {X Y : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] {K : Set X} (hK : IsCompact K) (E : Set (X × Y))
    (hE : ∀ x ∈ K, E ∈ 𝓝 (x,0)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∃ δ > 0,
      ∀ x ∈ U, ∀ r : Y, ‖r‖ ≤ δ → (x,r) ∈ E := by
  have hc : K ×ˢ ({0} : Set Y) ⊆ interior E := by
    rintro ⟨x,r⟩ ⟨hx,hr⟩
    have hr0 : r=0 := mem_singleton_iff.mp hr
    subst r
    exact mem_interior_iff_mem_nhds.mpr (hE x hx)
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK isCompact_singleton isOpen_interior hc
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨U,hU,hKU,r/2,half_pos hr,?_⟩
  intro x hx a ha
  apply interior_subset (hUV ⟨hx,hrV ?_⟩)
  rw [Metric.mem_ball,dist_zero_right]
  linarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

lemma continuousAt_conditionalSize {X : Type*} [TopologicalSpace X]
    {R j : ℝ} (hR : 0 ≤ R) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) (r : X → ℝ) (hr : Continuous r)
    {x : X} (hq : 0 < scalarQMoment (f x).1) (hs : 0 < scalarS j (f x))
    (hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1)
    (hB : 0 < j*scalarBMoment (f x).1+r x) :
    ContinuousAt (fun x=>conditionalScalarSize j (f x) (r x)) x := by
  have hq' := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hs' := ((continuous_scalarS j).comp hf).continuousAt (x := x)
  have hd' := ((continuous_scalarD j).comp hf).continuousAt (x := x)
  have hb' := (((continuous_const : Continuous (fun _ : X=>j)).mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))).add hr).continuousAt (x := x)
  have he' := (continuousAt_conditionalData hR f hf hdom r hr hq hs hS).2.norm
  exact (((((continuousAt_const.add hd'.abs).div hs' hs.ne').add
    (continuousAt_const.div hq' hq.ne')).add (continuousAt_const.div hs' hs.ne')).add
    (continuousAt_const.div hb' hB.ne')).add hb' |>.add he'

lemma continuousAt_augmentedGram {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin 3) (Fin 3) ℝ} {x : X} (hH : ContinuousAt H x) :
    ContinuousAt (fun x=>augmentedGram (ν := Unit) (H x)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  cases i with
  | inl i => cases k with
    | inl k => exact (continuousAt_pi.mp (continuousAt_pi.mp hH i) k)
    | inr k => exact continuousAt_const
  | inr i => cases k <;> exact continuousAt_const

lemma continuous_scalarPerturbedPoint {R t0 T : ℝ} :
    Continuous (@scalarPerturbedPoint R t0 T) := by
  unfold scalarPerturbedPoint
  fun_prop

lemma scalarPerturbedPoint_domain {R t0 T : ℝ} (z : ScalarTimeDomain R t0 T × (ℝ × ℝ)) :
    scalarPerturbedPoint z ∈ scalarMomentDomain R := ⟨z.1.1.2,mem_univ _⟩

lemma isCompact_scalarEqualitySet {j R t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht0 : 0 < t0) :
    IsCompact (scalarEqualitySet j R t0 T) := by
  let : CompactSpace (momentBall R) := isCompact_iff_compactSpace.mp (isCompact_momentBall R)
  have hcurve : Continuous (fun t : Icc t0 T=>scalarCurve j t) :=
    (continuous_scalarCurve_nonneg hj hj1).comp (continuous_subtype_val.subtype_mk (fun t=>ht0.le.trans t.2.1))
  exact (isClosed_eq (continuous_subtype_val.comp continuous_fst) (hcurve.comp continuous_snd)).isCompact

theorem scalar_conditional_neighborhood {j R t0 T ρ : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R) (ht0 : 0 < t0) (hρ : 0 < ρ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧
      scalarEqualitySet j R t0 T ⊆ U ∧ ∃ δ > 0,
      ∀ x ∈ U,∀ σ r : ℝ, |σ| ≤ δ → |r| ≤ δ →
      let p : ScalarPoint := ((x.1 : ProbabilityMeasure ℝ),(x.2 : ℝ),σ)
      0 < scalarQMoment p.1 ∧ 0 < scalarS j p ∧ 0 < j*scalarBMoment p.1+r ∧
      conditionalScalarSize j p r < L ∧
      ‖augmentedGram (ν := Unit) (scalarMomentGram p.1 (scalarD j p) (scalarS j p))-
        augmentedGram (ν := Unit) (limitingGram (scalarBMoment (scalarCurve j x.2))
          (scalarEMoment (scalarCurve j x.2)) (scalarFixedPoint j x.2))‖ < ρ ∧
      ‖conditionalMeanData j p r-curveCoefficient j x.2‖ < ρ := by
  let X := ScalarTimeDomain R t0 T
  let K := scalarEqualitySet j R t0 T
  let f : X × (ℝ × ℝ) → ScalarPoint := scalarPerturbedPoint
  let r : X × (ℝ × ℝ) → ℝ := fun z=>z.2.2
  have hf : Continuous f := continuous_scalarPerturbedPoint
  have hr : Continuous r := continuous_snd.comp continuous_snd
  have hd : ∀ z,f z ∈ scalarMomentDomain R := scalarPerturbedPoint_domain
  have hK : IsCompact K := isCompact_scalarEqualitySet hj hj1 ht0
  have heq (x : X) (hx : x ∈ K) : f (x,0)=(scalarCurve j x.2,(x.2:ℝ),0) := by
    change ((x.1:ProbabilityMeasure ℝ),(x.2:ℝ),0)=_
    rw [show (x.1:ProbabilityMeasure ℝ)=scalarCurve j x.2 from hx]
  have hpoint (x : X) (hx : x ∈ K) :
      0 < scalarQMoment (f (x,0)).1 ∧ 0 < scalarS j (f (x,0)) ∧
      0 < scalarS j (f (x,0))+j*scalarQMoment (f (x,0)).1 ∧
      0 < j*scalarBMoment (f (x,0)).1+r (x,0) := by
    rw [heq x hx,scalarQMoment_curve hj hj1 (ht0.le.trans x.2.2.1),scalarS_curve hj hj1 (ht0.le.trans x.2.2.1)]
    have hp := scalar_fixed_pos hj hj1 (ht0.trans_le x.2.2.1)
    exact ⟨hp.2,hp.1,add_pos hp.1 (mul_pos hj hp.2),by simpa [r] using mul_pos hj (scalarBMoment_pos (scalarCurve j x.2))⟩
  have hsize (x : X) (hx : x ∈ K) :
      ContinuousAt (fun z=>conditionalScalarSize j (f z) (r z)) (x,0) :=
    continuousAt_conditionalSize hR f hf hd r hr (hpoint x hx).1 (hpoint x hx).2.1
      (hpoint x hx).2.2.1 (hpoint x hx).2.2.2
  have hsizeK : ContinuousOn (fun x : X=>conditionalScalarSize j (f (x,0)) (r (x,0))) K := by
    intro x hx
    exact ((hsize x hx).comp (x := x) (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hsizeK
  let L := max 1 (M+1)
  have hL : 1 ≤ L := le_max_left _ _
  have hsmall (x : X) (hx : x ∈ K) : conditionalScalarSize j (f (x,0)) (r (x,0)) < L :=
    (lt_of_le_of_lt (hM (mem_image_of_mem _ hx)) (by linarith : M < M+1)).trans_le (le_max_right _ _)
  obtain ⟨hs,hq,hb,he,hkap,hc⟩ := continuous_curve_statistics (T := T) hj hj1 ht0
  let G : X × (ℝ × ℝ) → Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ := fun z=>
    augmentedGram (ν := Unit) (scalarMomentGram (f z).1 (scalarD j (f z)) (scalarS j (f z)))
  let G0 : X × (ℝ × ℝ) → Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ := fun z=>
    augmentedGram (ν := Unit) (limitingGram (scalarBMoment (scalarCurve j z.1.2))
      (scalarEMoment (scalarCurve j z.1.2)) (scalarFixedPoint j z.1.2))
  have hG0 : Continuous G0 := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply continuousAt_augmentedGram
    unfold limitingGram
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    have hb' := (hb.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    have he' := (he.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    have hs' := (hs.comp (continuous_snd.comp continuous_fst)).continuousAt (x := z)
    fin_cases i <;> fin_cases k <;> simp only [Matrix.of_apply,Matrix.cons_val,Fin.reduceFinMk] <;>
      fun_prop (disch := exact (scalar_fixed_pos hj hj1 (ht0.trans_le z.1.2.2.1)).1.ne')
  let E : Set (X × (ℝ × ℝ)) := {z |
    0 < scalarQMoment (f z).1 ∧ 0 < scalarS j (f z) ∧ 0 < j*scalarBMoment (f z).1+r z ∧
    conditionalScalarSize j (f z) (r z) < L ∧ ‖G z-G0 z‖ < ρ ∧
    ‖conditionalMeanData j (f z) (r z)-curveCoefficient j z.1.2‖ < ρ}
  have hE (x : X) (hx : x ∈ K) : E ∈ 𝓝 (x,0) := by
    have hpt := hpoint x hx
    have hqc := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := (x,0))
    have hsc := ((continuous_scalarS j).comp hf).continuousAt (x := (x,0))
    have hbc := (((continuous_const : Continuous (fun _ : X × (ℝ × ℝ)=>j)).mul (continuous_scalarBMoment.comp (continuous_fst.comp hf))).add hr).continuousAt (x := (x,0))
    have cg : ContinuousAt G (x,0) := by
      apply continuousAt_augmentedGram
      exact (continuousAt_scalarMomentGram (p := ((f (x,0)).1,scalarD j (f (x,0)),scalarS j (f (x,0)))) hpt.2.1.ne').comp
        (x := (x,0)) ((continuous_fst.comp hf).continuousAt.prodMk
        (((continuous_scalarD j).comp hf).continuousAt.prodMk hsc))
    have cm := (continuousAt_conditionalData hR f hf hd r hr hpt.1 hpt.2.1 hpt.2.2.1).1
    have hgzero : G (x,0)-G0 (x,0)=0 := by
      dsimp only [G,G0]
      rw [heq x hx,scalarD_curve hj hj1 (ht0.le.trans x.2.2.1),scalarS_curve hj hj1 (ht0.le.trans x.2.2.1),
        scalarMomentGram_curve hj hj1 (ht0.trans_le x.2.2.1)]
      exact sub_self _
    have hczero : conditionalMeanData j (f (x,0)) (r (x,0))-curveCoefficient j x.2=0 := by
      rw [heq x hx]
      change conditionalMeanData j (scalarCurve j x.2,(x.2:ℝ),0) 0-curveCoefficient j x.2=0
      rw [conditionalMeanData_curve hj hj1 (ht0.trans_le x.2.2.1),sub_self]
    have e1 := hqc.eventually_const_lt hpt.1
    have e2 := hsc.eventually_const_lt hpt.2.1
    have e3 := hbc.eventually_const_lt hpt.2.2.2
    have e4 := (hsize x hx).eventually_lt_const (hsmall x hx)
    have e5 := (cg.sub hG0.continuousAt).norm.eventually_lt_const (by change ‖G (x,0)-G0 (x,0)‖ < ρ; simpa only [hgzero,norm_zero] using hρ)
    have e6 := (cm.sub (hc.comp (continuous_snd.comp continuous_fst)).continuousAt).norm.eventually_lt_const (by change ‖conditionalMeanData j (f (x,0)) (r (x,0))-curveCoefficient j x.2‖ < ρ; simpa only [hczero,norm_zero] using hρ)
    exact e1.and (e2.and (e3.and (e4.and (e5.and e6))))
  obtain ⟨U,hU,hKU,δ,hδ,hδE⟩ := compact_perturbation_tube_norm hK E hE
  refine ⟨L,hL,U,hU,hKU,δ,hδ,?_⟩
  intro x hx σ r hσ hr
  exact hδE x hx (σ,r) (by simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using And.intro hσ hr)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalMiddleSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma continuousAt_conditionalMiddleSize {X : Type*} [TopologicalSpace X]
    {R : ℝ} (hR : 0 ≤ R) (j V W : ℝ) (f : X → ScalarPoint) (hf : Continuous f)
    (hdom : ∀ x,f x ∈ scalarMomentDomain R) {x : X}
    (hs : scalarS j (f x) ≠ 0) (hS : scalarS j (f x)+j*scalarQMoment (f x).1 ≠ 0) :
    ContinuousAt (fun x=>conditionalMiddleSize j V W (f x)) x := by
  have hq := (continuous_scalarQMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hb := (continuous_scalarBMoment.comp (continuous_fst.comp hf)).continuousAt (x := x)
  have hss := ((continuous_scalarS j).comp hf).continuousAt (x := x)
  have hSS : ContinuousAt (fun x=>scalarS j (f x)+j*scalarQMoment (f x).1) x := hss.add (continuousAt_const.mul hq)
  have ha := ((continuousOn_scalarA hR j).comp_continuous hf hdom).continuousAt (x := x)
  have hn : ContinuousAt (fun x=>(f x).2.1+(f x).2.2^2) x := by fun_prop
  have hk : ContinuousAt (fun x=>conditionalKappa j (f x)) x := (hn.div hss hs).sqrt
  have hl : ContinuousAt (fun x=>conditionalEll j (f x)) x := (hn.div hSS hS).sqrt
  unfold conditionalMiddleSize
  fun_prop (disch := assumption)

theorem conditionalMiddleSize_uniform {j R t0 T : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    (ht0 : 0 < t0) (V W : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (P : ProbabilityMeasure ℝ), P ∈ momentBall R →
      ∀ t ∈ Icc t0 T,∀ σ : ℝ, |σ| ≤ 1 → conditionalMiddleSize j V W (P,t,σ) ≤ L := by
  let X : Type := ↥(momentBall R) × ↥(Icc t0 T) × ↥(Icc (-1:ℝ) 1)
  let : CompactSpace (momentBall R) := isCompact_iff_compactSpace.mp (isCompact_momentBall R)
  let f : X → ScalarPoint := fun x=>((x.1:ProbabilityMeasure ℝ),(x.2.1:ℝ),(x.2.2:ℝ))
  have hf : Continuous f := by dsimp [f,X]; fun_prop
  have hdom : ∀ x,f x ∈ scalarMomentDomain R := fun (x : X)=>⟨x.1.2,mem_univ _⟩
  have hc : Continuous (fun x : X=>conditionalMiddleSize j V W (f x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have ht : 0 < (x.2.1:ℝ) := ht0.trans_le x.2.1.2.1
    have hs : 0 < scalarS j (f x) := by
      dsimp [scalarS,f]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ht (sq_nonneg _))
        (mul_nonneg hj (scalarQMoment_bounds _).1)
    have hS : 0 < scalarS j (f x)+j*scalarQMoment (f x).1 :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg hj (scalarQMoment_bounds _).1)
    exact continuousAt_conditionalMiddleSize hR j V W f hf hdom hs.ne' hS.ne'
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro P hP t ht σ hσ
  let x : X := (⟨P,hP⟩,⟨t,ht⟩,⟨σ,abs_le.mp hσ⟩)
  exact (hM (mem_image_of_mem _ (mem_univ x))).trans (le_max_right _ _)

lemma empirical_column_coefficient {n : ℕ} [NeZero n] {j t0 t T σ : ℝ}
    (hj : 0 ≤ j) (ht0 : 0 < t0) (ht : t ∈ Icc t0 T) (y : Fin n → ℝ) :
    (1+|scalarD j (empiricalLaw y,t,σ)|)/scalarS j (empiricalLaw y,t,σ) ≤
      max 1 ((1+|T|+j)/t0) := by
  have ht' : 0 < t := ht0.trans_le ht.1
  have hd : |scalarD j (empiricalLaw y,t,σ)| ≤ |T|+j := by
    apply (abs_add_le _ _).trans
    rw [abs_of_pos ht',abs_mul,abs_of_nonneg hj]
    have hh := mul_le_mul_of_nonneg_left (scalarM_bounds (empiricalLaw y)) hj
    have hT := ht.2.trans (le_abs_self T)
    nlinarith only [hh,hT]
  have hs : t0 ≤ scalarS j (empiricalLaw y,t,σ) := by
    dsimp [scalarS]
    exact ht.1.trans (le_add_of_nonneg_right (sq_nonneg σ) |>.trans
      (le_add_of_nonneg_right (mul_nonneg hj (scalarQMoment_bounds _).1)))
  apply le_trans _ (le_max_right _ _)
  exact div_le_div₀ (by positivity) (by linarith) ht0 hs
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalGramBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma gramCoordinates_bound {d s L : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (y : ℝ) (r : Fin 3) :
    |gramCoordinates d s y r| ≤ L*(1+|y|) := by
  have hLy : L ≤ L*(1+|y|) := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (abs_nonneg y)]
  fin_cases r
  · simpa [gramCoordinates] using hL.trans hLy
  · simpa [gramCoordinates] using (abs_tanh_lt_one y).le.trans (hL.trans hLy)
  · simp only [gramCoordinates,Matrix.cons_val,Fin.reduceFinMk,abs_div,abs_of_pos hs]
    apply (div_le_div_of_nonneg_right (abs_sub y d) hs.le).trans
    calc
      _ ≤ ((1+|d|)/s)*(1+|y|) := by
        rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hs]
        nlinarith [mul_nonneg (abs_nonneg d) (abs_nonneg y)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)

lemma gramCoordinates_product_bound {d s L : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (y : ℝ) (r k : Fin 3) :
    |gramCoordinates d s y r*gramCoordinates d s y k| ≤ 2*L^2*(1+y^2) := by
  rw [abs_mul]
  have hp := mul_le_mul (gramCoordinates_bound hs hL hd y r)
    (gramCoordinates_bound hs hL hd y k) (abs_nonneg _) (by positivity : 0 ≤ L*(1+|y|))
  have hx : (1+|y|)^2 ≤ 2*(1+y^2) := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg L)]

lemma diagonal_empirical_gram_entry {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ) (d s : ℝ) (r k : Fin 3) :
    matrixPair (diagonal a) (empiricalGramColumns y d s r).ofLp
      (empiricalGramColumns y d s k).ofLp=
      (n:ℝ)⁻¹*∑ i,a i*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  simp only [matrixPair,Matrix.mulVec_diagonal,empiricalGramColumns,WithLp.ofLp_toLp,dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hn0 : √(n:ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  field_simp
  rw [Real.sq_sqrt hnR.le]
  ring

theorem empirical_augmented_gram_comparison {n : ℕ} [NeZero n]
    (a y : Fin n → ℝ) {d s L D R ε ν : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (hD : 0 ≤ D) (hR : 1 ≤ R) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (ha : ∀ i,|a i-(1-tanh (y i)^2)| ≤ D)
    (hclose : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ))
    (htail : (∑ i,if R < |y i| then y i^2 else 0) ≤ ν*(n:ℝ)) :
    ‖diagonalAugmentedGram a (empiricalGramColumns y d s)-
      augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s)‖ ≤
      4*(2*L^2*(1+R^2)*ε+4*L^2*D*ν) := by
  have hn : 0 < n := NeZero.pos n
  have he (r k : Fin 3) : |matrixPair (diagonal a) (empiricalGramColumns y d s r).ofLp
      (empiricalGramColumns y d s k).ofLp-scalarMomentGram (empiricalLaw y) d s r k| ≤
      2*L^2*(1+R^2)*ε+4*L^2*D*ν := by
    rw [diagonal_empirical_gram_entry hn,scalarMomentGram_empirical]
    have hsmall (i : Fin n) (hi : |y i| ≤ R) :
        |gramCoordinates d s (y i) r*gramCoordinates d s (y i) k| ≤ 2*L^2*(1+R^2) := by
      apply (gramCoordinates_product_bound hs hL hd (y i) r k).trans
      have hy : y i^2 ≤ R^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y i)) (by linarith : 0 ≤ R)).mpr hi
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb := normalized_weighted_moment_comparison hn a (fun i=>1-tanh (y i)^2) y
      (fun i=>gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)
      (H := 2*L^2*(1+R^2)) (C := 2*L^2) (D := D) (R := R) (by positivity)
      (by positivity) hD hR hε ha hsmall (fun i=>gramCoordinates_product_bound hs hL hd (y i) r k)
      hclose htail
    have hid : (n:ℝ)⁻¹*(∑ i,a i*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)-
        (n:ℝ)⁻¹*(∑ i,(1-tanh (y i)^2)*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)=
        (∑ i,(a i-(1-tanh (y i)^2))*(gramCoordinates d s (y i) r*gramCoordinates d s (y i) k))/(n:ℝ) := by
      rw [← mul_sub,← Finset.sum_sub_distrib,div_eq_mul_inv,mul_comm _ (n:ℝ)⁻¹]
      congr 1
      apply Finset.sum_congr rfl
      intro i _;ring
    rw [hid]
    convert hb using 1 <;> first | rfl | ring
  have hb0 : 0 ≤ 2*L^2*(1+R^2)*ε+4*L^2*D*ν := by positivity
  have hb := frobenius_le_card_bound (M := diagonalAugmentedGram a (empiricalGramColumns y d s)-
    augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s))
    (ε := 2*L^2*(1+R^2)*ε+4*L^2*D*ν) (by positivity) (by
      intro r k
      cases r with
      | inl r => cases k with
        | inl k => exact he r k
        | inr k => change |(0:ℝ)-0| ≤ _; simpa only [sub_zero,abs_zero] using hb0
      | inr r => cases k with
        | inl k => change |(0:ℝ)-0| ≤ _; simpa only [sub_zero,abs_zero] using hb0
        | inr k => change |(1:ℝ)-1| ≤ _; simpa only [sub_self,abs_zero] using hb0)
  simpa using hb
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalConditionalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma conditionalSize_bounds {j : ℝ} {p : ScalarPoint} {r L : ℝ}
    (hq : 0 < scalarQMoment p.1) (hs : 0 < scalarS j p)
    (hB : 0 < j*scalarBMoment p.1+r) (hsize : conditionalScalarSize j p r < L) :
    (1+|scalarD j p|)/scalarS j p < L ∧ 1/scalarQMoment p.1 < L ∧
    1/scalarS j p < L ∧ 1/(j*scalarBMoment p.1+r) < L ∧
    j*scalarBMoment p.1+r < L ∧ ‖conditionalScalarData j p‖ < L := by
  have h1 : 0 ≤ (1+|scalarD j p|)/scalarS j p := by positivity
  have h2 : 0 ≤ 1/scalarQMoment p.1 := by positivity
  have h3 : 0 ≤ 1/scalarS j p := by positivity
  have h4 : 0 ≤ 1/(j*scalarBMoment p.1+r) := by positivity
  have h5 := norm_nonneg (conditionalScalarData j p)
  unfold conditionalScalarSize at hsize
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

lemma empiricalGramColumns_norm {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    {d s L R : ℝ} (hs : 0 < s) (hL : 1 ≤ L) (hR : 0 ≤ R)
    (hd : (1+|d|)/s ≤ L) (hy : ∑ i,y i^2 ≤ R^2*(n:ℝ)) (r : Fin 3) :
    ‖empiricalGramColumns y d s r‖ ≤ 2*L*(R+1) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb (i : Fin n) : (gramCoordinates d s (y i) r)^2 ≤ 2*L^2*(1+y i^2) := by
    simpa only [← sq,abs_pow, sq_abs] using gramCoordinates_product_bound hs hL hd (y i) r r
  have hsq : ‖empiricalGramColumns y d s r‖^2 ≤ 2*L^2*(1+R^2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [empiricalGramColumns,PiLp.toLp_apply,div_pow,Real.sq_sqrt hnR.le]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ i,2*L^2*(1+y i^2) := Finset.sum_le_sum (fun i _=>hb i)
      _ = 2*L^2*((n:ℝ)+∑ i,y i^2) := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; simp
      _ ≤ 2*L^2*((n:ℝ)+R^2*(n:ℝ)) := mul_le_mul_of_nonneg_left (add_le_add_right hy _) (by positivity)
      _ = _ := by ring
  have hcmp : 2*L^2*(1+R^2) ≤ (2*L*(R+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg L) hR, sq_nonneg (L*R)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hsq.trans hcmp)

lemma empiricalUnit_unit {n : ℕ} [NeZero n] (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp=1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hsum : ∑ i,tanh (y i)^2=(n:ℝ)*scalarQMoment (empiricalLaw y) := by
    simpa only [scalarQMoment,Fintype.card_fin] using (card_mul_integral_empiricalLaw y (fun x=>tanh x^2)).symm
  simp only [empiricalUnit,WithLp.ofLp_toLp,dotProduct,← sq,div_pow,Real.sq_sqrt (mul_nonneg hn.le hq.le)]
  rw [← Finset.sum_div,hsum,div_self (mul_pos hn hq).ne']

lemma empiricalUnit_norm {n : ℕ} [NeZero n] (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    ‖empiricalUnit y (scalarQMoment (empiricalLaw y))‖=1 := by
  have hh := empiricalUnit_unit y hq
  have he : ‖empiricalUnit y (scalarQMoment (empiricalLaw y))‖^2=1 := by
    simpa only [EuclideanSpace.real_norm_sq_eq,dotProduct,← sq] using hh
  nlinarith [norm_nonneg (empiricalUnit y (scalarQMoment (empiricalLaw y)))]

lemma normalized_average_l2 {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hd : ∑ i,d i^2 ≤ ε^2*(n:ℝ)) :
    |(n:ℝ)⁻¹*∑ i,d i| ≤ ε := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : sqrt (∑ i,d i^2) ≤ ε*sqrt (n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    simpa only [mul_pow,Real.sq_sqrt hnR.le] using hd
  have hh := (Finset.abs_sum_le_sum_abs d Finset.univ).trans (sum_abs_le_sqrt_card_l2 d)
  simp only [Fintype.card_fin] at hh
  have hh' : |∑ i,d i| ≤ ε*(n:ℝ) := by
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left hs (sqrt_nonneg _)).trans_eq
    calc
      _ = ε*(sqrt (n:ℝ))^2 := by ring
      _ = _ := by rw [sq_sqrt hnR.le]
  rw [abs_mul,abs_of_pos (inv_pos.mpr hnR)]
  have hp := mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr hnR.le)
  convert hp using 1 <;> first | rfl | field_simp

lemma empirical_mass_close {n : ℕ} [NeZero n] (a y : Fin n → ℝ) {j ε : ℝ}
    (hj : 0 ≤ j) (hε : 0 ≤ ε)
    (hd : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ)) :
    |j/(n:ℝ)*∑ i,a i-j*scalarBMoment (empiricalLaw y)| ≤ j*ε := by
  have hb : scalarBMoment (empiricalLaw y)=(n:ℝ)⁻¹*∑ i,(1-tanh (y i)^2) := by
    rw [scalarBMoment_integral]
    simpa only [scalarGramVariance,Fintype.card_fin] using integral_empiricalLaw y (fun x=>1-tanh x^2)
  rw [hb]
  have he : j/(n:ℝ)*∑ i,a i-j*((n:ℝ)⁻¹*∑ i,(1-tanh (y i)^2))=
      j*((n:ℝ)⁻¹*∑ i,(a i-(1-tanh (y i)^2))) := by simp only [Finset.sum_sub_distrib]; ring
  rw [he,abs_mul,abs_of_nonneg hj]
  exact mul_le_mul_of_nonneg_left (normalized_average_l2 (NeZero.pos n) _ hε hd) hj
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix
open scoped BigOperators Matrix.Norms.Frobenius

lemma augmentedToleranceConstant_pos {L : ℝ} (hL : 0 ≤ L) :
    0 < augmentedToleranceConstant L := by unfold augmentedToleranceConstant; positivity

lemma augmentedGramTolerance_bound {B L ε : ℝ} (hB : 0 < B) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) (hb : B ≤ L) (hi : 1/B ≤ L) :
    augmentedGramTolerance B ε ≤ augmentedToleranceConstant L*ε := by
  have hL0 : 0 ≤ L := by linarith
  have hir : (sqrt B)⁻¹ ≤ L+1 := by
    have hs : (sqrt B)⁻¹=sqrt B⁻¹ := (sqrt_inv B).symm
    rw [hs]
    have hh := sq_sqrt (inv_pos.mpr hB).le
    have hh' : B⁻¹ ≤ L := by simpa only [one_div] using hi
    nlinarith [sq_nonneg (sqrt B⁻¹-1)]
  have hB2 : B^2 ≤ L^2 := pow_le_pow_left₀ hB.le hb 2
  have ht1 : (sqrt B)⁻¹*(1+B) ≤ (L+1)*(1+L) :=
    mul_le_mul hir (by linarith) (by positivity) (by linarith)
  have ht2 : B⁻¹*(1+2*B+B^2) ≤ L*(1+2*L+L^2) :=
    mul_le_mul (by simpa only [one_div] using hi) (by linarith) (by positivity) hL0
  unfold augmentedGramTolerance augmentedToleranceConstant
  have h1 := mul_le_mul_of_nonneg_right ht1 hε
  have h2 := mul_le_mul_of_nonneg_right ht2 hε
  nlinarith

lemma conditionalMeanData_hermitian (j : ℝ) (p : ScalarPoint) (r : ℝ) :
    (conditionalMeanData j p r).IsHermitian := by
  exact conditionalCoefficient_hermitian _ _ _ _
lemma conditionalScalarData_hermitian (j : ℝ) (p : ScalarPoint) :
    (conditionalScalarData j p).IsHermitian := by
  exact conditionalCoefficient_hermitian _ _ _ _
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma diagonal_mass_margin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) {m r A : ℝ} (ha : ∀ i,0 ≤ a i) (hA : ∀ i,a i ≤ A)
    (hr : |r| * A ≤ m) (hH : (H-(2*m) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) :
    (H-r • diagonal a-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hd : (diagonal (fun i=>m-r*a i)).PosSemidef := Matrix.PosSemidef.diagonal (fun i=>by
    change 0 ≤ m-r*a i
    have hh : r*a i ≤ |r| * A := (mul_le_mul_of_nonneg_right (le_abs_self r) (ha i)).trans
      (mul_le_mul_of_nonneg_left (hA i) (abs_nonneg r))
    linarith)
  convert hH.add_posSemidef hd using 1
  all_goals try with_reducible_and_instances rfl
  ext i k
  by_cases hik : i=k
  · subst k; simp; ring
  · simp [hik]

lemma empirical_moment_vector_bound {n : ℕ} [NeZero n] {R : ℝ}
    (hR : 0 ≤ R) (y : Fin n → ℝ) (hy : empiricalLaw y ∈ momentBall R) :
    ∑ i,y i^2 ≤ (R+1)^2*(n:ℝ) := by
  have hh := momentBall_integral_le hR hy
  rw [integral_empiricalLaw] at hh
  simp only [Fintype.card_fin] at hh
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hp := mul_le_mul_of_nonneg_left hh hn.le
  have hp' : ∑ i,y i^2 ≤ R*(n:ℝ) := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul,mul_comm (n:ℝ) R] using hp
  have hR' : R ≤ (R+1)^2 := by nlinarith [sq_nonneg R]
  exact hp'.trans (mul_le_mul_of_nonneg_right hR' hn.le)

lemma empirical_cutoff_gram_small {n : ℕ} [NeZero n] (a y : Fin n → ℝ)
    {A L ε ν R1 ρ d s : ℝ}
    (ha : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) (hA : 0 ≤ A)
    (hs : 0 < s) (hL : 1 ≤ L) (hd : (1+|d|)/s ≤ L)
    (hR1 : 1 ≤ R1) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (haclose : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ))
    (hy : (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ))
    (hεgram : 8*L^2*(1+R1^2)*ε ≤ ρ/8)
    (hνgram : 16*L^2*(A+1)*ν ≤ ρ/8) :
    ‖diagonalAugmentedGram a (empiricalGramColumns y d s)-
      augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s)‖ ≤ ρ/4 := by
  have hdiff (i : Fin n) : |a i-(1-tanh (y i)^2)| ≤ A+1 := by
    have hv0 := tanh_sq_lt_one (y i)
    have hv1 := sq_nonneg (tanh (y i))
    exact abs_le.mpr ⟨by linarith [ha i],by linarith [haA i]⟩
  have hg := empirical_augmented_gram_comparison a y hs hL hd
    (by positivity : 0 ≤ A+1) hR1 hε hν hdiff haclose hy
  apply hg.trans
  nlinarith

lemma gram_close_by_quarters {α : Type*} [SeminormedAddCommGroup α] (a b c : α)
    {ρ : ℝ} (hab : ‖a-b‖ ≤ ρ/4) (hbc : ‖b-c‖ < ρ/4) : ‖a-c‖ < ρ/2 := by
  exact (norm_sub_le_norm_sub_add_norm_sub a b c).trans_lt (by linarith)

theorem conditional_empirical_fixed_tail {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
    (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ¬(conditionalEmpiricalCore j x.2 σ a y g-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
      101*exp (-c*(n:ℝ)) := by
  have hA0 : 0 < A := by linarith
  obtain ⟨hs,hq,hb,he,hκ,_⟩ := continuous_curve_statistics (T := T) hj hj1 ht0
  obtain ⟨δ,ρ,hδ,_,hρ,htail⟩ := compact_conditional_uniform_tail hj hj1 hA0 hsub
    (fun t : Icc t0 T=>scalarBMoment (scalarCurve j t))
    (fun t : Icc t0 T=>scalarEMoment (scalarCurve j t))
    (fun t : Icc t0 T=>scalarFixedPoint j t) (fun t : Icc t0 T=>scalarQ j t)
    (fun t : Icc t0 T=>curveKappa j t) hb he hs hq hκ
    (fun t=>scalarBMoment_pos _) (fun t=>scalarBMoment_le_one _) (fun t=>scalarEMoment_nonneg _)
    (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).1)
    (fun t=>(scalar_fixed_pos hj hj1 (ht0.trans_le t.2.1)).2)
    (fun t=>curveKappa_sq hj hj1 (ht0.trans_le t.2.1))
  obtain ⟨L,hL,U,hU,hKU,σ0,hσ0,hnb⟩ := scalar_conditional_neighborhood (R := R) (T := T) hj hj1 hR ht0 (by positivity : 0 < ρ/4)
  let m := δ*((1-sqrt j*A)^2/4)/2
  have hm : 0 < m := by dsimp [m]; positivity
  let terr := 16*L^2*(A+1)
  have hterr : 0 < terr := by dsimp [terr]; positivity
  let ν := ρ/(8*terr)
  have hν : 0 < ν := by dsimp [ν]; positivity
  let Vbound := 2*L*(R+2)+1
  have hV : 0 ≤ Vbound := by dsimp [Vbound]; positivity
  let K := augmentedToleranceConstant L
  have hK : 0 < K := augmentedToleranceConstant_pos (by linarith)
  let εg := ρ/(4*K)
  let τ := ρ/(4*(L+1))
  have hεg : 0 < εg := by dsimp [εg]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨c,N,hc,hN,hfixed⟩ := htail Vbound hV εg τ hεg hτ
  refine ⟨m,ν,σ0,hm,hν,hσ0,U,hU,hKU,?_⟩
  intro R1 hR1
  let berr := 8*L^2*(1+R1^2)
  have hberr : 0 < berr := by dsimp [berr]; positivity
  let ε := min (σ0/(j+1)) (min (ρ/(8*berr)) (m/(j*A+1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεσ : ε*(j+1) ≤ σ0 := (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hεgram : berr*ε ≤ ρ/8 := by
    have hh : ε ≤ ρ/(8*berr) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 8*berr)).mp hh
    nlinarith only [hh']
  have hεmass : ε*(j*A+1) ≤ m := (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,c,N,hε,hc,hN,?_⟩
  intro n _ hn x hx y hP hy σ hσ a ha haA haclose
  let p : ScalarPoint := (empiricalLaw y,(x.2:ℝ),σ)
  let BA := j/(n:ℝ)*∑ i,a i
  let B := j*scalarBMoment (empiricalLaw y)
  let r := BA-B
  have hr : |r| ≤ j*ε := empirical_mass_close a y hj.le hε.le haclose
  have hrσ : |r| ≤ σ0 := hr.trans (by nlinarith only [hεσ,hε.le])
  have hnbe := hnb x hx σ r hσ hrσ
  rw [← hP] at hnbe
  change 0 < scalarQMoment p.1 ∧ 0 < scalarS j p ∧ 0 < B+r ∧
    conditionalScalarSize j p r < L ∧ _ ∧ _ at hnbe
  have hBr : B+r=BA := by dsimp [r]; ring
  have hBA : 0 < BA := by simpa only [hBr] using hnbe.2.2.1
  have hd := conditionalSize_bounds hnbe.1 hnbe.2.1 hnbe.2.2.1 hnbe.2.2.2.1
  have hBAle : BA < L := by
    have hh := hd.2.2.2.2.1
    change B+r<L at hh
    simpa only [hBr] using hh
  have hBAinv : 1/BA < L := by
    have hh := hd.2.2.2.1
    change 1/(B+r)<L at hh
    simpa only [hBr] using hh
  have htol : augmentedGramTolerance BA εg < ρ/2 := by
    apply (augmentedGramTolerance_bound hBA hL hεg.le hBAle.le hBAinv.le).trans_lt
    have heq : augmentedToleranceConstant L*εg=ρ/4 := by
      dsimp [εg]
      change K*(ρ/(4*K))=ρ/4
      field_simp
    rw [heq]; linarith
  have hEbound : τ*‖conditionalScalarData j p‖ < ρ/2 := by
    apply (mul_lt_mul_of_pos_left hd.2.2.2.2.2 hτ).trans
    have hL0 : 0 < L+1 := by linarith
    have hh : τ*(L+1)=ρ/4 := by dsimp [τ]; field_simp
    nlinarith only [hh,hτ,hρ]
  have hvecmom := empirical_moment_vector_bound hR y (by rw [hP]; exact x.1.2)
  let cols := empiricalGramColumns y (scalarD j p) (scalarS j p)
  let u := empiricalUnit y (scalarQMoment p.1)
  have hpbound : ∀ k,‖cols k‖ ≤ Vbound := fun k=>(empiricalGramColumns_norm (NeZero.pos n) y hnbe.2.1 hL (by linarith : 0 ≤ R+1) hd.1.le hvecmom k).trans (by dsimp [Vbound]; linarith)
  have hubound : ‖u‖ ≤ Vbound := by
    rw [empiricalUnit_norm y hnbe.1]
    dsimp [Vbound]
    have hp : 0 ≤ 2*L*(R+2) := by positivity
    linarith
  have hunit : u.ofLp⬝ᵥu.ofLp=1 := empiricalUnit_unit y hnbe.1
  have hνgram : 16*L^2*(A+1)*ν ≤ ρ/8 := by
    have ht : terr*ν=ρ/8 := by dsimp [ν]; field_simp
    exact ht.le
  have hgsmall := empirical_cutoff_gram_small a y ha haA hA0.le hnbe.2.1 hL hd.1.le
    hR1 hε.le hν.le haclose hy hεgram hνgram
  have hGram : ‖diagonalAugmentedGram a cols-augmentedGram (ν := Unit)
      (limitingGram (scalarBMoment (scalarCurve j x.2)) (scalarEMoment (scalarCurve j x.2))
        (scalarFixedPoint j x.2))‖ < ρ/2 := by
    exact gram_close_by_quarters _ _ _ hgsmall hnbe.2.2.2.2.1
  have hCoef : ‖conditionalMeanData j p r-curveCoefficient j x.2‖ < ρ/2 :=
    hnbe.2.2.2.2.2.trans (by linarith)
  have hprob := hfixed n hn a ha haA hBA htol cols u hpbound hubound hunit x.2
    (conditionalMeanData j p r) (conditionalScalarData j p)
    (conditionalMeanData_hermitian j p r) (conditionalScalarData_hermitian j p) hEbound hGram hCoef
  apply le_trans (measureReal_mono (s₂ := {g | ¬(conditionalBase j a g-
      pathDiagonal a 1*conditionalUpdateColumns j a cols u g*
      (conditionalMeanData j p r+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • conditionalScalarData j p)*
      (conditionalUpdateColumns j a cols u g)ᵀ*pathDiagonal a 1-
      (δ*((1-sqrt j*A)^2/4)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef}) ?_ (measure_ne_top _ _)) hprob
  intro g hg
  contrapose! hg
  simp only [Set.mem_ofPred_eq,not_not] at hg ⊢
  have hrm : |r| * A ≤ m := by
    apply (mul_le_mul_of_nonneg_right hr hA0.le).trans
    nlinarith only [hεmass,hε.le]
  have hm2 : 2*m=δ*((1-sqrt j*A)^2/4) := by dsimp [m]; ring
  have hh := diagonal_mass_margin _ a ha haA hrm (by rw [hm2]; exact hg)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [conditionalEmpiricalCore,p,B,BA,r,cols,u]
  congr 1
  module
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalHessianJoined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_half_holder {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |sqrt a-sqrt b| ≤ sqrt |a-b| := by
  have hsq : (sqrt a-sqrt b)^2 ≤ |a-b| := by
    rcases le_total a b with hab | hab
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      have hp := mul_nonneg (sqrt_nonneg a) (sub_nonneg.mpr (sqrt_le_sqrt hab))
      nlinarith [sq_sqrt ha,sq_sqrt hb]
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      have hp := mul_nonneg (sqrt_nonneg b) (sub_nonneg.mpr (sqrt_le_sqrt hab))
      nlinarith [sq_sqrt ha,sq_sqrt hb]
  simpa only [sqrt_sq_eq_abs] using sqrt_le_sqrt hsq

lemma diagonalRoot_norm {a : ι → ℝ} {M : ℝ} (_hM : 0 ≤ M) (ha : ∀ i,a i ≤ M) :
    ‖diagonalRoot a‖ ≤ sqrt M := by
  rw [diagonalRoot,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (sqrt_nonneg M)).mpr
    (fun i => by rw [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]; exact sqrt_le_sqrt (ha i))

lemma diagonalRoot_half_holder {a b : ι → ℝ} {ζ : ℝ} (_hζ : 0 ≤ ζ)
    (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (hab : ∀ i,|a i-b i| ≤ ζ) :
    ‖diagonalRoot a-diagonalRoot b‖ ≤ sqrt ζ := by
  rw [diagonalRoot,diagonalRoot,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (sqrt_nonneg ζ)).mpr (fun i =>
    (sqrt_half_holder (ha i) (hb i)).trans (sqrt_le_sqrt (hab i)))

theorem diagonalHessian_half_holder {a b : ι → ℝ} {M ζ L : ℝ}
    (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hL : 0 ≤ L)
    (ha : ∀ i,a i ∈ Set.Icc 0 M) (hb : ∀ i,b i ∈ Set.Icc 0 M)
    (hab : ∀ i,|a i-b i| ≤ ζ) (K : Matrix ι ι ℝ) (hK : ‖K‖ ≤ L) :
    ‖diagonalHessian a K-diagonalHessian b K‖ ≤ 2*sqrt M*L*sqrt ζ := by
  have hD := diagonalRoot_norm hM (fun i => (ha i).2)
  have hE := diagonalRoot_norm hM (fun i => (hb i).2)
  have hDE := diagonalRoot_half_holder hζ (fun i => (ha i).1) (fun i => (hb i).1) hab
  have heq : diagonalHessian a K-diagonalHessian b K=
      -((diagonalRoot a-diagonalRoot b)*K*diagonalRoot a+
        diagonalRoot b*K*(diagonalRoot a-diagonalRoot b)) := by
    simp only [diagonalHessian,Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [heq,norm_neg]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans
  have hb₁ : ‖(diagonalRoot a-diagonalRoot b)*K‖ ≤ sqrt ζ*L :=
    (norm_mul_le _ _).trans (mul_le_mul hDE hK (norm_nonneg _) (sqrt_nonneg _))
  have hb₂ : ‖diagonalRoot b*K‖ ≤ sqrt M*L :=
    (norm_mul_le _ _).trans (mul_le_mul hE hK (norm_nonneg _) (sqrt_nonneg _))
  apply (add_le_add (mul_le_mul hb₁ hD (norm_nonneg _) (by positivity))
    (mul_le_mul hb₂ hDE (norm_nonneg _) (by positivity))).trans_eq
  ring

lemma diagonalHessian_hermitian (a : ι → ℝ) {K : Matrix ι ι ℝ} (hK : K.IsHermitian) :
    (diagonalHessian a K).IsHermitian := by
  unfold diagonalHessian Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
    diagonalRoot,Matrix.diagonal_conjTranspose,star_trivial,hK.eq]
  simp only [Matrix.mul_assoc]

lemma matrix_quadratic_op_bound (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (M*ᵥx)| ≤ ‖M‖*(x⬝ᵥx) := by
  let y : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  have hh := abs_real_inner_le_norm y (M.toEuclideanLin.toContinuousLinearMap y)
  have hn := M.toEuclideanLin.toContinuousLinearMap.le_opNorm y
  have hin : inner ℝ y (M.toEuclideanLin.toContinuousLinearMap y)=x⬝ᵥ(M*ᵥx) := by
    change (∑ i,(M*ᵥx) i*x i)=∑ i,x i*(M*ᵥx) i
    apply Finset.sum_congr rfl; intro i _; ring
  have hy : ‖y‖^2=x⬝ᵥx := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [y,dotProduct,pow_two]
  rw [hin] at hh
  calc
    _ ≤ ‖y‖*‖M.toEuclideanLin.toContinuousLinearMap y‖ := hh
    _ ≤ ‖y‖*(‖M‖*‖y‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by rw [← hy]; ring

theorem hermitian_margin_transfer {S T : Matrix ι ι ℝ} (hS : S.IsHermitian)
    (_hT : T.IsHermitian) {c d : ℝ} (hd : ‖S-T‖ ≤ d)
    (hc : (T-c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (S-(c-d) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩
  · exact hS.sub (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))
  · intro x
    have hq := matrix_quadratic_op_bound (S-T) x
    have hp := hc.dotProduct_mulVec_nonneg x
    have hxx : 0 ≤ x⬝ᵥx := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have hbd := mul_le_mul_of_nonneg_right hd hxx
    simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      dotProduct_sub,dotProduct_smul,smul_eq_mul] at hp hq ⊢
    rcases abs_le.mp (hq.trans hbd) with ⟨hl,_⟩
    nlinarith only [hp,hl]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma empirical_columns_one {n : ℕ} (y : Fin n → ℝ) (d s : ℝ) {q : ℝ}
    (hq : 0 < q) : sqrt q • (empiricalUnit y q).ofLp=(empiricalGramColumns y d s 1).ofLp := by
  have hsq : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  ext i
  simp only [empiricalUnit,empiricalGramColumns,gramCoordinates,WithLp.ofLp_toLp,
    Pi.smul_apply,smul_eq_mul,Matrix.cons_val,sqrt_mul (Nat.cast_nonneg n)]
  field_simp

lemma empirical_columns_two {n : ℕ} (y : Fin n → ℝ) (d : ℝ) {s : ℝ}
    (hs : 0 < s) : (sqrt s)⁻¹ • (sqrt s • (empiricalGramColumns y d s 2).ofLp)=
      (empiricalGramColumns y d s 2).ofLp := by
  rw [inv_smul_smul₀ (sqrt_pos.mpr hs).ne']

lemma empirical_columns_matrix {n : ℕ} (y : Fin n → ℝ) (d : ℝ) {q s : ℝ}
    (hq : 0 < q) (hs : 0 < s) (N : Fin n → ℝ) :
    conditionalColumns (empiricalGramColumns y d s 0).ofLp
      (sqrt q • (empiricalUnit y q).ofLp)
      ((sqrt s)⁻¹ • (sqrt s • (empiricalGramColumns y d s 2).ofLp)) N=
      extendColumns (fun r=>(empiricalGramColumns y d s r).ofLp) N := by
  rw [empirical_columns_one y d s hq,empirical_columns_two y d hs]
  ext i k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => rfl

lemma pathDiagonal_one_eq_sqrt {n : ℕ} (a : Fin n → ℝ) : pathDiagonal a 1=diagonalRoot a := by
  simp only [pathDiagonal,diagonalRoot,Real.sqrt_one,one_mul]

lemma pathDiagonal_sq {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i,0 ≤ a i) :
    pathDiagonal a 1*pathDiagonal a 1=diagonal a := by
  rw [pathDiagonal_one_eq_sqrt,diagonalRoot,Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp only [← pow_two,Real.sq_sqrt (ha i)]

theorem conditionalEmpiricalCore_eq_hessian {n : ℕ} [NeZero n] (j t σ : ℝ)
    (a y : Fin n → ℝ) (g : MatrixCoordinates (Fin n) → ℝ)
    (ha : ∀ i,0 ≤ a i) (hq : 0 < scalarQMoment (empiricalLaw y))
    (hs : 0 < scalarS j (empiricalLaw y,t,σ)) (hBA : 0 < j/(n:ℝ)*∑ i,a i) :
    conditionalEmpiricalCore j t σ a y g=diagonalHessian a (empiricalConditionalMiddle j t σ y g) := by
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let BA := j/(n:ℝ)*∑ i,a i
  have hh := conditional_hessian_rank_form (j/(n:ℝ)) j (scalarA j p) B
    (conditionalKappa j p) (conditionalEll j p) (q := q) (s := s)
    (S := s+j*q) hq hs hBA
    (empiricalGramColumns y (scalarD j p) s 0).ofLp
    (empiricalUnit y q).ofLp
    (sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp)
    (pathDiagonal a 1) g
  dsimp only at hh
  rw [empirical_columns_matrix y (scalarD j p) hq hs,pathDiagonal_sq a ha] at hh
  have hB : B+(BA-B)=BA := by ring
  have hbil : goeBilinear (j/(n:ℝ)) (empiricalUnit y q).ofLp (empiricalUnit y q).ofLp g=
      matrixBilinear (goeMatrix (j/(n:ℝ)) g) (empiricalUnit y q) (empiricalUnit y q) := by
    rw [matrixBilinear_eq_pair]
    rfl
  rw [hbil] at hh
  symm
  convert hh using 1
  · simp only [diagonalHessian,empiricalConditionalMiddle,p,q,s,B,pathDiagonal_one_eq_sqrt,
      Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_smul,
      Matrix.smul_mul,Matrix.mul_one]
    abel
  · simp only [conditionalEmpiricalCore,conditionalBase,conditionalUpdateColumns,
      conditionalMeanData,conditionalScalarData,p,q,s,B,BA] at *
    rw [hB]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SparseCubeNet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Set Real
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
lemma option_support_weight [DecidableEq ι] (h : ℝ) (f : ι → Option κ) :
    (∏ i, if (f i).isSome then h else 1) = h^(optionSupport f).card := by
  rw [← Finset.prod_filter]
  simp [optionSupport]

lemma option_weight_sum [DecidableEq ι] (h : ℝ) :
    (∑ f : ι → Option κ, h^(optionSupport f).card)=(1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) := by
  simp only [← option_support_weight]
  rw [← Fintype.prod_sum (fun (_ : ι) (o : Option κ) => if o.isSome then h else 1)]
  simp [Fintype.sum_option]

theorem sparse_option_count [DecidableEq ι] [DecidableEq κ]
    {h α : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (s : Finset (ι → Option κ))
    (hs : ∀ f ∈ s, ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ)) :
    (s.card:ℝ) ≤ exp (((Fintype.card κ:ℝ)*h-α*log h)*(Fintype.card ι:ℝ)) := by
  have hb : (s.card:ℝ)*exp (α*(Fintype.card ι:ℝ)*log h) ≤
      (1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) := by
    calc
      _ = ∑ _f ∈ s, exp (α*(Fintype.card ι:ℝ)*log h) := by simp
      _ ≤ ∑ f ∈ s, h^(optionSupport f).card := by
        apply Finset.sum_le_sum
        intro f hf
        rw [mul_comm (α*(Fintype.card ι:ℝ)) (log h),← Real.rpow_def_of_pos hh,← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (hs f hf)
      _ ≤ ∑ f : ι → Option κ, h^(optionSupport f).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => pow_nonneg hh.le _)
      _ = _ := option_weight_sum h
  have ht : 0 < 1+(Fintype.card κ:ℝ)*h := by positivity
  have he : (1+(Fintype.card κ:ℝ)*h)^(Fintype.card ι) ≤
      exp ((Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*h) := by
    rw [← Real.exp_log ht,← exp_nat_mul]
    apply exp_le_exp.mpr
    have hl := log_le_sub_one_of_pos ht
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]
  have hb := (le_div_iff₀ (exp_pos _)).mpr hb
  apply hb.trans
  calc
    _ ≤ exp ((Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*h) /
        exp (α*(Fintype.card ι:ℝ)*log h) := div_le_div_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_sub]; congr 1; ring

theorem sparse_option_small_entropy {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      [DecidableEq κ] (s : Finset (ι → Option κ)),
      (∀ f ∈ s, ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ)) →
      (s.card:ℝ) ≤ exp (ε*(Fintype.card ι:ℝ)) := by
  let h : ℝ := min (1/2) (ε/(2*((Fintype.card κ:ℝ)+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hlog : 0 < -log h := neg_pos.mpr (log_neg hh hh1)
  let α := ε/(2*(-log h))
  refine ⟨α,by positivity,?_⟩
  intro ι _ _ _ s hs
  apply (sparse_option_count hh hh1.le s hs).trans
  apply exp_le_exp.mpr
  have hNh : (Fintype.card κ:ℝ)*h ≤ ε/2 := by
    have hd := (le_div_iff₀ (show 0 < 2*((Fintype.card κ:ℝ)+1) by positivity)).mp
      (show h ≤ ε/(2*((Fintype.card κ:ℝ)+1)) from min_le_right _ _)
    nlinarith
  have ha : α*(-log h)=ε/2 := by dsimp [α]; field_simp [ne_of_lt (log_neg hh hh1)]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

omit [Fintype κ] in

theorem sparse_cube_approx [DecidableEq ι] {M ζ α : ℝ} (hζ : 0 < ζ)
    (v a : ι → ℝ) (grid : κ → ℝ) (ha : ∀ i, a i ∈ Icc 0 M)
    (hgrid : ∀ x ∈ Icc (0:ℝ) M, ∃ k, |x-grid k| ≤ ζ)
    (hsq : (∑ i,(a i-v i)^2) ≤ α*ζ^2*(Fintype.card ι:ℝ)) :
    ∃ f : ι → Option κ,
      ((optionSupport f).card:ℝ) ≤ α*(Fintype.card ι:ℝ) ∧
      (∀ i, |a i-optionCube v grid f i| ≤ ζ) ∧
      (∀ i, |optionCube v grid f i-v i| ≤ 2*|a i-v i|) := by
  classical
  choose k hk using (fun i => hgrid (a i) (ha i))
  let f : ι → Option κ := fun i => if ζ < |a i-v i| then some (k i) else none
  have hsupp : optionSupport f = Finset.univ.filter (fun i => ζ < |a i-v i|) := by
    ext i
    simp [optionSupport,f]
  have hb : ((optionSupport f).card:ℝ)*ζ^2 ≤ ∑ i,(a i-v i)^2 := by
    calc
      _ = ∑ i ∈ optionSupport f, ζ^2 := by simp
      _ ≤ ∑ i ∈ optionSupport f, (a i-v i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp (hsupp ▸ hi)).2
        nlinarith [sq_abs (a i-v i)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine ⟨f,?_,?_,?_⟩
  · apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hζ)).mp
    calc
      _ ≤ _ := hb.trans hsq
      _ = _ := by ring
  · intro i
    by_cases hi : ζ < |a i-v i|
    · simpa [optionCube,f,hi] using hk i
    · simpa [optionCube,f,hi] using le_of_not_gt hi
  · intro i
    by_cases hi : ζ < |a i-v i|
    · simp only [optionCube,f,hi,ite_eq_left,Option.elim_some]
      have h := abs_sub_le (grid (k i)) (a i) (v i)
      rw [abs_sub_comm (grid (k i)) (a i)] at h
      linarith [hk i]
    · simp [optionCube,f,hi,abs_nonneg]

omit [Fintype ι] [Fintype κ] in
lemma optionCube_bounds {M : ℝ} (v : ι → ℝ) (grid : κ → ℝ)
    (hv : ∀ i, v i ∈ Icc 0 M) (hg : ∀ k,grid k ∈ Icc 0 M) (f : ι → Option κ) :
    ∀ i, optionCube v grid f i ∈ Icc 0 M := by
  intro i
  cases h : f i with
  | none => simpa [optionCube,h] using hv i
  | some k => simpa [optionCube,h] using hg k

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators

lemma interval_mesh {M ζ : ℝ} (hζ : 0 < ζ) :
    ∃ s : Finset ℝ, (∀ x ∈ s,x ∈ Icc (0:ℝ) M) ∧
      ∀ x ∈ Icc (0:ℝ) M,∃ y ∈ s,|x-y| ≤ ζ := by
  classical
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) M)).finite_cover_balls hζ
  refine ⟨hfin.toFinset,fun x hx => hs (hfin.mem_toFinset.mp hx),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  exact ⟨y,hfin.mem_toFinset.mpr hy,(show |x-y| < ζ from Metric.mem_ball.mp hxy).le⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SparseShrink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators

theorem sparse_uniform_exponential_shrink {M ζ r : ℝ} (hζ : 0 < ζ) (hr : 0 < r) :
    ∃ ε₀ : ℝ,0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsFiniteMeasure μ] (n : ℕ) (v : Fin n → ℝ) (_hv : ∀ i,v i ∈ Icc 0 M)
      (E : Set Ω) (GoodHigh GoodLow : (Fin n → ℝ) → Ω → Prop) (C : ℝ),
      0 ≤ C →
      (∀ b, (∀ i,b i ∈ Icc 0 M) → (∑ i,(b i-v i)^2) ≤ 4*ε^2*(n:ℝ) →
        μ.real {ω | ¬GoodHigh b ω} ≤ C*exp (-r*(n:ℝ))) →
      (∀ ω ∈ E,∀ a b, (∀ i,a i ∈ Icc 0 M) → (∀ i,b i ∈ Icc 0 M) →
        (∀ i,|a i-b i| ≤ ζ) → GoodHigh b ω → GoodLow a ω) →
      μ.real {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ≤ μ.real Eᶜ+C*exp (-(r/2)*(n:ℝ)) := by
  classical
  obtain ⟨grid,hgrid,hcover⟩ := interval_mesh (M := M) hζ
  let κ := {x : ℝ // x ∈ grid}
  obtain ⟨α,hα,hcount⟩ := sparse_option_small_entropy (κ := κ) (half_pos hr)
  let ε₀ := sqrt α*ζ
  have hε₀ : 0 < ε₀ := mul_pos (sqrt_pos.mpr hα) hζ
  have heq₀ : ε₀^2=α*ζ^2 := by dsimp [ε₀]; rw [mul_pow,sq_sqrt hα.le]
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεle
  have heq : ε^2 ≤ α*ζ^2 := by rw [← heq₀]; exact pow_le_pow_left₀ hε.le hεle 2
  intro Ω _ μ _ n v hv E GoodHigh GoodLow C hC hfixed hnear
  let val : κ → ℝ := Subtype.val
  let s : Finset (Fin n → Option κ) := Finset.univ.filter (fun f =>
    ((optionSupport f).card:ℝ) ≤ α*(n:ℝ) ∧
      (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ))
  have hsize : (s.card:ℝ) ≤ exp ((r/2)*(n:ℝ)) := by
    simpa only [Fintype.card_fin] using hcount (Fin n) s (fun f hf => by simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hf).2.1)
  let B : (Fin n → Option κ) → Set Ω := fun f => {ω | ¬GoodHigh (optionCube v val f) ω}
  have hsub : {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ⊆ Eᶜ ∪ ⋃ f ∈ s,B f := by
    intro ω ⟨a,ha,ha2,hbad⟩
    by_cases hE : ω ∈ E
    · obtain ⟨f,hf,hap,hfp⟩ := sparse_cube_approx hζ v a val ha
        (fun x hx => by obtain ⟨y,hy,hyx⟩ := hcover x hx; exact ⟨⟨y,hy⟩,hyx⟩)
        (by
          simp only [Fintype.card_fin]
          exact ha2.trans (mul_le_mul_of_nonneg_right heq (Nat.cast_nonneg n)))
      have hb : ∀ i,optionCube v val f i ∈ Icc 0 M :=
        optionCube_bounds v val hv (fun k => hgrid k.val k.property) f
      have hd : (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ) := by
        calc
          _ ≤ ∑ i,4*(a i-v i)^2 := by
            apply Finset.sum_le_sum; intro i _
            have h := hfp i
            have hh := mul_self_le_mul_self (abs_nonneg (optionCube v val f i-v i)) h
            nlinarith only [hh,sq_abs (optionCube v val f i-v i),sq_abs (a i-v i)]
          _ = 4*(∑ i,(a i-v i)^2) := by rw [Finset.mul_sum]
          _ ≤ _ := by linarith
      have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [Fintype.card_fin] using And.intro hf hd⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨f,hfs,fun hg => hbad (hnear ω hE a _ ha hb hap hg)⟩)
    · exact Or.inl hE
  have hsum : (∑ f ∈ s,μ.real (B f)) ≤ (s.card:ℝ)*(C*exp (-r*(n:ℝ))) := by
    calc
      _ ≤ ∑ _f ∈ s,C*exp (-r*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro f hf
        exact hfixed _ (optionCube_bounds v val hv (fun k => hgrid k.val k.property) f)
          (Finset.mem_filter.mp hf).2.2
      _ = _ := by simp
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measureReal_biUnion_finset_le s B).trans
  apply hsum.trans
  calc
    _ ≤ exp ((r/2)*(n:ℝ))*(C*exp (-r*(n:ℝ))) := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm (exp _) C,mul_assoc,← exp_add]; congr 2; ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator

lemma conditional_mesh_size {A L m : ℝ} (hA : 0 < A) (hL : 0 < L) (hm : 0 < m) :
    ∃ ζ : ℝ, 0 < ζ ∧ 2*sqrt A*L*sqrt ζ ≤ m/2 := by
  let r := m/(4*sqrt A*L)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  rw [sqrt_sq hr.le]
  dsimp [r]
  have hd : sqrt A ≠ 0 := (sqrt_pos.mpr hA).ne'
  field_simp
  ring_nf
  rfl

theorem conditional_sparse_uniform {j A L m c : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hL : 0 < L) (hm : 0 < m) (hc : 0 < c) :
    ∃ ε0 : ℝ,0 < ε0 ∧ ∀ ε : ℝ,0 < ε → ε ≤ ε0 →
    ∀ (n : ℕ) [NeZero n] (v : Fin n → ℝ), (∀ i,v i ∈ Icc 0 A) →
    ∀ K : (MatrixCoordinates (Fin n) → ℝ) → Matrix (Fin n) (Fin n) ℝ,
    (∀ g,(K g).IsHermitian) →
    (∀ g,opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1 → opNorm (K g) ≤ L) →
    (∀ b, (∀ i,b i ∈ Icc 0 A) → (∑ i,(b i-v i)^2) ≤ 4*ε^2*(n:ℝ) →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
        {g | ¬(diagonalHessian b (K g)-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
        101*exp (-c*(n:ℝ))) →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (K g)-(m/2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
      103*exp (-(min (1/(π^2*j)) (c/2))*(n:ℝ)) := by
  obtain ⟨ζ,hζ,hζm⟩ := conditional_mesh_size hA hL hm
  obtain ⟨ε0,hε0,hsmall⟩ := sparse_uniform_exponential_shrink (M := A) hζ hc
  refine ⟨ε0,hε0,?_⟩
  intro ε hε hεle n _ v hv K hK hKn hfixed
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let E : Set (MatrixCoordinates (Fin n) → ℝ) := {g | opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1}
  have hevent : μ.real Eᶜ ≤ 2*exp (-(n:ℝ)/(π^2*j)) := by
    change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ¬‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖ ≤ 2*sqrt j+1} ≤ _
    simp only [not_le]
    simpa only [one_pow,_root_.neg_one_mul,Fintype.card_fin] using
      (goe_norm_tail (ι := Fin n) hj (by norm_num : (0:ℝ) ≤ 1))
  have hsparse := hsmall ε hε hεle (MatrixCoordinates (Fin n) → ℝ) μ n v hv E
    (fun b g=>(diagonalHessian b (K g)-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (fun a g=>(diagonalHessian a (K g)-(m/2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    101 (by norm_num) hfixed (by
      intro g hg a b ha hb hab hh
      have hnorm : ‖K g‖ ≤ L := hKn g hg
      have hd := diagonalHessian_half_holder hA.le hζ.le hL.le ha hb hab (K g) hnorm
      have htrans := hermitian_margin_transfer (diagonalHessian_hermitian a (hK g))
        (diagonalHessian_hermitian b (hK g)) (hd.trans hζm) hh.posSemidef
      have hhalf : m-m/2=m/2 := by ring
      simpa only [hhalf] using htrans)
  apply hsparse.trans
  have h1 : -(n:ℝ)/(π^2*j) ≤ -(min (1/(π^2*j)) (c/2))*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (1/(π^2*j)) (c/2)) (Nat.cast_nonneg n)
    calc
      _ = -((1/(π^2*j))*(n:ℝ)) := by ring
      _ ≤ _ := by linarith only [h]
  have h2 : -(c/2)*(n:ℝ) ≤ -(min (1/(π^2*j)) (c/2))*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1/(π^2*j)) (c/2)) (Nat.cast_nonneg n)
    linarith only [h]
  have h1' := exp_le_exp.mpr h1
  have h2' := exp_le_exp.mpr h2
  nlinarith only [hevent,h1',h2']
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ConditionalMiddleNorm
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

lemma real_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

lemma real_opNorm_smul (c : ℝ) (M : Matrix ι ι ℝ) : opNorm (c • M)=|c| * opNorm M := by
  unfold opNorm
  rw [map_smul,map_smul,norm_smul,Real.norm_eq_abs]

lemma operator_vecMulVec_le (u v : EuclideanSpace ℝ ι) :
    opNorm (vecMulVec u.ofLp v.ofLp) ≤ ‖u‖*‖v‖ := by
  apply (operator_le_frobenius _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun k _=>sq_nonneg _))),
    mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [vecMulVec_apply,Real.norm_eq_abs,abs_mul,mul_pow,sq_abs]
  rw [Finset.sum_mul]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma operator_mulVec_norm_le (W : Matrix ι ι ℝ) (u : EuclideanSpace ℝ ι) :
    ‖WithLp.toLp 2 (W*ᵥu.ofLp)‖ ≤ opNorm W*‖u‖ := by
  exact W.toEuclideanLin.toContinuousLinearMap.le_opNorm u

lemma goeBilinear_norm_bound (r : ℝ) (u : EuclideanSpace ℝ ι)
    (g : MatrixCoordinates ι → ℝ) :
    |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm (goeMatrix r g)*‖u‖^2 := by
  have hh := matrix_quadratic_op_bound (goeMatrix r g) u.ofLp
  change |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm (goeMatrix r g)*(u.ofLp⬝ᵥu.ofLp) at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,← sq]

lemma conditionalBlockMatrix_norm {r j q s S a B κ ell : ℝ}
    (u Z : EuclideanSpace ℝ ι) (g : MatrixCoordinates ι → ℝ) (hu : ‖u‖=1) :
    opNorm (conditionalBlockMatrix r j q s S a B κ ell u.ofLp Z.ofLp g) ≤
      (1+2*|κ-1|+|ell-2*κ+1|)*opNorm (goeMatrix r g)+
      2*(|j*sqrt (q/s)| * ‖Z‖+|j*a/s|)+|2*j*(a+B*q)/S| := by
  let W := goeMatrix r g
  let Wu : EuclideanSpace ℝ ι := WithLp.toLp 2 (W*ᵥu.ofLp)
  let w : EuclideanSpace ℝ ι := (j*sqrt (q/s)) • Z-(j*a/s) • u
  have hW : 0 ≤ opNorm W := norm_nonneg _
  have hwu : ‖Wu‖ ≤ opNorm W := by simpa only [hu,mul_one] using operator_mulVec_norm_le W u
  have huu : opNorm (vecMulVec u.ofLp u.ofLp) ≤ 1 := by simpa only [hu,mul_one] using operator_vecMulVec_le u u
  have h1 : opNorm (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp) ≤ 2*opNorm W := by
    apply (real_opNorm_add _ _).trans
    have ha := operator_vecMulVec_le u Wu
    have hb := operator_vecMulVec_le Wu u
    rw [hu,one_mul] at ha
    rw [hu,mul_one] at hb
    linarith
  have hα : |goeBilinear r u.ofLp u.ofLp g| ≤ opNorm W := by
    simpa only [hu,one_pow,mul_one] using goeBilinear_norm_bound r u g
  have hw : ‖w‖ ≤ |j*sqrt (q/s)| * ‖Z‖+|j*a/s| := by
    apply (norm_sub_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one]
    rfl
  have h2 : opNorm (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp) ≤
      2*(|j*sqrt (q/s)| * ‖Z‖+|j*a/s|) := by
    apply (real_opNorm_add _ _).trans
    have ha := operator_vecMulVec_le u w
    have hb := operator_vecMulVec_le w u
    rw [hu,one_mul] at ha
    rw [hu,mul_one] at hb
    linarith
  have he : conditionalBlockMatrix r j q s S a B κ ell u.ofLp Z.ofLp g=
      (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)+
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)+
        (2*j*(a+B*q)/S) • vecMulVec u.ofLp u.ofLp := by
    unfold conditionalBlockMatrix
    rw [goeBlockResidual_expand]
    dsimp [W,Wu,w]
    abel
  rw [he]
  have hn := real_opNorm_add ((W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)+
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)) ((2*j*(a+B*q)/S) • vecMulVec u.ofLp u.ofLp)
  apply hn.trans
  have hd := real_opNorm_add (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp)+
        ((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)
      (vecMulVec u.ofLp w.ofLp+vecMulVec w.ofLp u.ofLp)
  have hc := real_opNorm_add (W+(κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp))
      (((ell-2*κ+1)*goeBilinear r u.ofLp u.ofLp g) • vecMulVec u.ofLp u.ofLp)
  have hb := real_opNorm_add W ((κ-1) • (vecMulVec u.ofLp Wu.ofLp+vecMulVec Wu.ofLp u.ofLp))
  rw [real_opNorm_smul] at hb
  rw [real_opNorm_smul,abs_mul] at hc
  rw [real_opNorm_smul]
  have hp1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (κ-1))
  have hp2 : |ell-2*κ+1| * |goeBilinear r u.ofLp u.ofLp g| * opNorm (vecMulVec u.ofLp u.ofLp) ≤
      |ell-2*κ+1| * opNorm W := by
    apply (mul_le_mul_of_nonneg_left huu (by positivity)).trans
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left hα (abs_nonneg _)
  have hp3 := mul_le_mul_of_nonneg_left huu (abs_nonneg (2*j*(a+B*q)/S))
  nlinarith only [hd,hc,hb,hp1,hp2,hp3,h2]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ConditionalEmpiricalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma outer_symmetric {ι : Type*} (x : ι → ℝ) : (vecMulVec x x).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply,star_trivial,vecMulVec_apply]
  ring

lemma outer_sum_symmetric {ι : Type*} (x y : ι → ℝ) : (vecMulVec x y+vecMulVec y x).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply,star_trivial,Matrix.add_apply,vecMulVec_apply]
  ring

lemma conditionalBlockMatrix_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r j q s S a B κ ell : ℝ) (u Z : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    (conditionalBlockMatrix r j q s S a B κ ell u Z g).IsHermitian := by
  unfold conditionalBlockMatrix
  rw [goeBlockResidual_expand]
  have hh := (goeMatrix_symm r g).add ((outer_sum_symmetric u (goeMatrix r g*ᵥu)).smul
    (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (κ-1))))
  have hh' := hh.add ((outer_symmetric u).smul (R := ℝ)
    (isSelfAdjoint_iff.mpr (star_trivial ((ell-2*κ+1)*goeBilinear r u u g))))
  convert (hh'.add (outer_sum_symmetric u ((j*sqrt (q/s)) • Z-(j*a/s) • u))).add
    ((outer_symmetric u).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (2*j*(a+B*q)/S)))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  abel

lemma empiricalConditionalMiddle_hermitian {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y : Fin n → ℝ) (g : MatrixCoordinates (Fin n) → ℝ) :
    (empiricalConditionalMiddle j t σ y g).IsHermitian := by
  unfold empiricalConditionalMiddle
  exact (((conditionalBlockMatrix_hermitian _ _ _ _ _ _ _ _ _ _ _ _).add
    ((outer_symmetric _).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))).add
    ((outer_symmetric _).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))).sub
    (Matrix.isHermitian_one.smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial _)))

lemma empiricalConditionalMiddle_norm {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y : Fin n → ℝ) {V W : ℝ} (hV : 0 ≤ V)
    (g : MatrixCoordinates (Fin n) → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y))
    (hcols : ∀ k, ‖empiricalGramColumns y (scalarD j (empiricalLaw y,t,σ))
      (scalarS j (empiricalLaw y,t,σ)) k‖ ≤ V)
    (hW : opNorm (goeMatrix (j/(n:ℝ)) g) ≤ W) :
    opNorm (empiricalConditionalMiddle j t σ y g) ≤
      conditionalMiddleSize j V W (empiricalLaw y,t,σ) := by
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let u := empiricalUnit y q
  let X := empiricalGramColumns y (scalarD j p) s 0
  let Z := sqrt s • empiricalGramColumns y (scalarD j p) s 2
  have hu : ‖u‖=1 := empiricalUnit_norm y hq
  have hZ : ‖Z‖ ≤ sqrt s*V := by
    dsimp [Z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hcols 2) (sqrt_nonneg _)
  have hX : opNorm (vecMulVec X.ofLp X.ofLp) ≤ V^2 := by
    apply (operator_vecMulVec_le X X).trans
    simpa only [pow_two] using mul_le_mul (hcols 0) (hcols 0) (norm_nonneg _) hV
  have hu' : opNorm (vecMulVec u.ofLp u.ofLp) ≤ 1 := by
    simpa only [hu,mul_one] using operator_vecMulVec_le u u
  have hI : opNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 := by
    simpa only [Matrix.diagonal_one] using opNorm_diagonal_le (ι := Fin n) zero_le_one (d := fun _=>1)
      (fun _=>by norm_num)
  have hb := conditionalBlockMatrix_norm (r := j/(n:ℝ)) (j := j) (q := q) (s := s)
    (S := s+j*q) (a := scalarA j p) (B := B) (κ := conditionalKappa j p)
    (ell := conditionalEll j p) u Z g hu
  have hc : opNorm (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g) ≤
      (1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)*W+
      2*(|j*sqrt (q/s)| * (sqrt s*V)+|j*scalarA j p/s|)+|2*j*(scalarA j p+B*q)/(s+j*q)| := by
    apply hb.trans
    have hn := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)
    have hz := mul_le_mul_of_nonneg_left hZ (abs_nonneg (j*sqrt (q/s)))
    linarith
  change opNorm (_+j • vecMulVec X.ofLp X.ofLp+(2*j*q) • vecMulVec u.ofLp u.ofLp-B • 1) ≤ _
  rw [sub_eq_add_neg,← neg_smul]
  apply (real_opNorm_add _ _).trans
  have h1 := real_opNorm_add (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g+j • vecMulVec X.ofLp X.ofLp)
    ((2*j*q) • vecMulVec u.ofLp u.ofLp)
  have h2 := real_opNorm_add (conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p) B
      (conditionalKappa j p) (conditionalEll j p) u.ofLp Z.ofLp g)
    (j • vecMulVec X.ofLp X.ofLp)
  rw [real_opNorm_smul] at h1 h2
  rw [real_opNorm_smul,abs_neg]
  have h3 := mul_le_mul_of_nonneg_left hX (abs_nonneg j)
  have h4 := mul_le_mul_of_nonneg_left hu' (abs_nonneg (2*j*q))
  have h5 := mul_le_mul_of_nonneg_left hI (abs_nonneg B)
  dsimp [conditionalMiddleSize,p,q,s,B,u,X,Z] at hc h1 h2 h3 h4 h5 ⊢
  nlinarith only [hc,h1,h2,h3,h4,h5]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarS_pos_of_time {j t σ : ℝ} (hj : 0 ≤ j) (ht : 0 < t) (P : ProbabilityMeasure ℝ) :
    0 < scalarS j (P,t,σ) :=
  add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ht (sq_nonneg _))
    (mul_nonneg hj (scalarQMoment_bounds _).1)

theorem empiricalConditionalMiddle_uniform_norm {j R t0 T : ℝ}
    (hj : 0 ≤ j) (hR : 0 ≤ R) (ht0 : 0 < t0) (W : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (n : ℕ) [NeZero n] (y : Fin n → ℝ),
      empiricalLaw y ∈ momentBall R → 0 < scalarQMoment (empiricalLaw y) →
      ∀ t ∈ Icc t0 T,∀ σ : ℝ, |σ| ≤ 1 →
      ∀ g : MatrixCoordinates (Fin n) → ℝ, opNorm (goeMatrix (j/(n:ℝ)) g) ≤ W →
      opNorm (empiricalConditionalMiddle j t σ y g) ≤ L := by
  let K := max 1 ((1+|T|+j)/t0)
  have hK : 1 ≤ K := le_max_left _ _
  let V := 2*K*(R+2)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨L,hL,hbd⟩ := conditionalMiddleSize_uniform (T := T) hj hR ht0 V W
  refine ⟨L,hL,?_⟩
  intro n _ y hy hq t ht σ hσ g hg
  have hs := scalarS_pos_of_time (σ := σ) hj (ht0.trans_le ht.1) (empiricalLaw y)
  have hcol : ∀ k,‖empiricalGramColumns y (scalarD j (empiricalLaw y,t,σ))
      (scalarS j (empiricalLaw y,t,σ)) k‖ ≤ V := by
    intro k
    convert empiricalGramColumns_norm (NeZero.pos n) y hs hK (by linarith : 0 ≤ R+1)
      (empirical_column_coefficient hj ht0 ht y) (empirical_moment_vector_bound hR y hy) k using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [V]; ring
  exact (empiricalConditionalMiddle_norm j t σ y hV g hq hcol hg).trans (hbd _ hy t ht σ hσ)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalWellDefined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

theorem empirical_conditional_wellDefined {j R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∃ σ0 ε0 : ℝ, 0 < σ0 ∧ 0 < ε0 ∧ ∀ x ∈ U,∀ σ : ℝ, |σ| ≤ σ0 →
      ∀ (n : ℕ) [NeZero n] (y a : Fin n → ℝ), empiricalLaw y=(x.1:ProbabilityMeasure ℝ) →
      (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε0^2*(n:ℝ) →
      0 < scalarQMoment (empiricalLaw y) ∧ 0 < scalarS j (empiricalLaw y,(x.2:ℝ),σ) ∧
      0 < j/(n:ℝ)*∑ i,a i := by
  obtain ⟨L,hL,U,hU,hKU,δ,hδ,hnb⟩ := scalar_conditional_neighborhood (R := R) (T := T)
    hj hj1 hR ht0 (by norm_num : (0:ℝ)<1)
  let ε := δ/(j+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : j*ε ≤ δ := by
    have hh : (j+1)*ε=δ := by dsimp [ε]; field_simp
    nlinarith only [hh,hε.le]
  refine ⟨U,hU,hKU,δ,ε,hδ,hε,?_⟩
  intro x hx σ hσ n _ y a hP hclose
  let r := j/(n:ℝ)*∑ i,a i-j*scalarBMoment (empiricalLaw y)
  have hr : |r| ≤ δ := (empirical_mass_close a y hj.le hε.le hclose).trans hεδ
  have hh := hnb x hx σ r hσ hr
  rw [← hP] at hh
  refine ⟨hh.1,hh.2.1,?_⟩
  have hB : j*scalarBMoment (empiricalLaw y)+r=j/(n:ℝ)*∑ i,a i := by dsimp [r]; ring
  simpa only [hB] using hh.2.2.1
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma four_radius_sq_le {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ/2) :
    4*ε^2 ≤ δ^2 := by
  have hh := mul_self_le_mul_self (by linarith : 0 ≤ 2*ε) (by linarith : 2*ε ≤ δ)
  nlinarith only [hh]

theorem conditional_empirical_simultaneous_oai {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
        (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (empiricalConditionalMiddle j x.2 σ y g)-
          m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
      103*exp (-c*(n:ℝ)) := by
  obtain ⟨m,ν,σf,hm,hν,hσf,Uf,hUf,hKUf,hfixed⟩ :=
    conditional_empirical_fixed_tail (T := T) hj hj1 hA hsub hR ht0
  obtain ⟨Uw,hUw,hKUw,σw,εw,hσw,hεw,hwell⟩ :=
    empirical_conditional_wellDefined (T := T) hj hj1 hR ht0
  obtain ⟨L,hL,hnorm⟩ := empiricalConditionalMiddle_uniform_norm (T := T) hj.le hR ht0 (2*sqrt j+1)
  let σ0 := min 1 (min σf σw)
  have hσ0 : 0 < σ0 := by dsimp [σ0]; positivity
  refine ⟨m/2,ν,σ0,half_pos hm,hν,hσ0,Uf ∩ Uw,hUf.inter hUw,?_,?_⟩
  · exact fun x hx=>⟨hKUf hx,hKUw hx⟩
  intro R1 hR1
  obtain ⟨εf,c,N,hεf,hc,hN,hfix⟩ := hfixed R1 hR1
  obtain ⟨εs,hεs,hsparse⟩ := conditional_sparse_uniform hj (by linarith : 0 < A)
    (by linarith : 0 < L) hm hc
  let ε := min εs (min (εf/2) (εw/2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεs' : ε ≤ εs := min_le_left _ _
  have hεf' : ε ≤ εf/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεw' : ε ≤ εw/2 := (min_le_right _ _).trans (min_le_right _ _)
  let c0 := min (1/(π^2*j)) (c/2)
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  refine ⟨ε,c0,N,hε,hc0,hN,?_⟩
  intro n _ hn x hx y hP hy σ hσ
  have hσ1 : |σ| ≤ 1 := hσ.trans (min_le_left _ _)
  have hσf' : |σ| ≤ σf := hσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσw' : |σ| ≤ σw := hσ.trans ((min_le_right _ _).trans (min_le_right _ _))
  let v : Fin n → ℝ := fun i=>1-tanh (y i)^2
  have hv (i : Fin n) : v i ∈ Icc 0 A := ⟨by dsimp [v]; linarith [tanh_sq_lt_one (y i)],
    by dsimp [v]; linarith [sq_nonneg (tanh (y i))]⟩
  have hzero : (∑ i,(v i-(1-tanh (y i)^2))^2) ≤ εw^2*(n:ℝ) := by
    simp only [v,sub_self,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero]
    positivity
  have hpos := hwell x hx.2 σ hσw' n y v hP hzero
  have hnorm' : ∀ g,opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1 →
      opNorm (empiricalConditionalMiddle j x.2 σ y g) ≤ L :=
    hnorm n y (by rw [hP]; exact x.1.2) hpos.1 x.2 x.2.2 σ hσ1
  apply hsparse ε hε hεs' n v hv (empiricalConditionalMiddle j x.2 σ y)
    (empiricalConditionalMiddle_hermitian j x.2 σ y) hnorm'
  intro b hb hbclose
  have hclosef : (∑ i,(b i-(1-tanh (y i)^2))^2) ≤ εf^2*(n:ℝ) :=
    hbclose.trans (mul_le_mul_of_nonneg_right (four_radius_sq_le hε.le hεf') (Nat.cast_nonneg n))
  have hclosew : (∑ i,(b i-(1-tanh (y i)^2))^2) ≤ εw^2*(n:ℝ) :=
    hbclose.trans (mul_le_mul_of_nonneg_right (four_radius_sq_le hε.le hεw') (Nat.cast_nonneg n))
  have hposb := hwell x hx.2 σ hσw' n y b hP hclosew
  have heq (g : MatrixCoordinates (Fin n) → ℝ) := conditionalEmpiricalCore_eq_hessian j x.2 σ b y g
    (fun i=>(hb i).1) hposb.1 hposb.2.1 hposb.2.2
  have hh := hfix n hn x hx.1 y hP hy σ hσf' b (fun i=>(hb i).1) (fun i=>(hb i).2) hclosef
  simp only [heq] at hh
  exact hh
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.conditional_empirical_simultaneous_oai := @OAI.SKGap.conditional_empirical_simultaneous_oai
