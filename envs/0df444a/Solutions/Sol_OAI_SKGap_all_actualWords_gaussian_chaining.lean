-- Prove2me | solution 1 for OAI.SKGap.all_actualWords_gaussian_chaining
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:15.735129+00:00
-- url     : https://prove2.me/submissions/0ad587bb-df8d-4b8f-89d8-2c2721746fa3

import Mathlib
import Definitions.Def_OAIQ072A000

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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_IntervalMesh
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology

lemma intervalMeshIndex_bounds (t : Icc (0:ℝ) 1) (k : ℕ) :
    intervalMeshPoint k (intervalMeshIndex t k) ≤ (t:ℝ) ∧
    (t:ℝ)-intervalMeshPoint k (intervalMeshIndex t k) ≤ (1/4:ℝ)^k := by
  have hq : (0:ℝ) < 4^k := by positivity
  have hl := Nat.floor_le (mul_nonneg t.property.1 (show (0:ℝ) ≤ 4^k by positivity))
  have hu := Nat.lt_floor_add_one ((t:ℝ)*(4:ℝ)^k)
  change (⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k ≤ (t:ℝ) ∧ _
  constructor
  · exact (div_le_iff₀ hq).mpr hl
  · change (t:ℝ)-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k ≤ _
    rw [one_div_pow]
    apply (le_div_iff₀ hq).mpr
    have he : ((t:ℝ)-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ)/(4:ℝ)^k)*(4:ℝ)^k =
        (t:ℝ)*(4:ℝ)^k-(⌊(t:ℝ)*(4:ℝ)^k⌋₊:ℝ) := by field_simp
    rw [he]
    linarith only [hu]

lemma intervalMeshIndex_tendsto (t : Icc (0:ℝ) 1) :
    Tendsto (fun k=>intervalMeshPoint k (intervalMeshIndex t k)) atTop (𝓝 (t:ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _=>dist_nonneg) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num))
  intro k
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (intervalMeshIndex_bounds t k).1)]
  linarith only [(intervalMeshIndex_bounds t k).2]

lemma intervalMeshIndex_increment (t : Icc (0:ℝ) 1) (k : ℕ) :
    |intervalMeshPoint (k+1) (intervalMeshIndex t (k+1))-
      intervalMeshPoint k (intervalMeshIndex t k)| ≤ 2*(1/4:ℝ)^k := by
  have h₁ := intervalMeshIndex_bounds t k
  have h₂ := intervalMeshIndex_bounds t (k+1)
  have hq : (0:ℝ) ≤ (1/4:ℝ)^k := by positivity
  rw [pow_succ] at h₂
  apply abs_le.mpr
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hq]

lemma intervalMesh_edges_card (k : ℕ)
    (s : Finset (Fin (4^k+1)×Fin (4^(k+1)+1))) :
    s.card ≤ 16^(k+1) := by
  have hc := Finset.card_le_univ s
  simp only [Fintype.card_prod,Fintype.card_fin] at hc
  apply hc.trans
  have hq : 1 ≤ 4^k := one_le_pow₀ (by omega)
  have hq' : 4^(k+1)=4^k*4 := pow_succ _ _
  have he : 16^(k+1)=16*(4^k)^2 := by
    have h : (16:ℕ)=4^2 := by norm_num
    rw [pow_succ,h,← pow_mul,← pow_mul]
    ring_nf
  rw [hq',he]
  nlinarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology BigOperators
variable {α : Type*}

lemma boxMeshIndex_tendsto (θ : α→Icc (0:ℝ) 1) :
    Tendsto (fun k=>boxMeshPoint k (boxMeshIndex θ k)) atTop (𝓝 θ) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_subtype_rng.mpr (intervalMeshIndex_tendsto (θ i))

variable [Fintype α]
lemma boxMeshIndex_increment (θ : α→Icc (0:ℝ) 1) (k : ℕ) :
    dist (boxMeshPoint (k+1) (boxMeshIndex θ (k+1))) (boxMeshPoint k (boxMeshIndex θ k))≤2*(1/4:ℝ)^k := by
  apply (dist_pi_le_iff (by positivity : (0:ℝ)≤2*(1/4:ℝ)^k)).mpr
  intro i
  exact intervalMeshIndex_increment (θ i) k

variable [DecidableEq α]

lemma boxMesh_edges_card (k : ℕ)
    (s : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1)))) :
    s.card≤16^((k+1)*Fintype.card α) := by
  apply (Finset.card_le_univ s).trans
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,←mul_pow]
  have hh := intervalMesh_edges_card k (Finset.univ : Finset (Fin (4^k+1)×Fin (4^(k+1)+1)))
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hh
  simpa only [pow_mul] using Nat.pow_le_pow_left hh (Fintype.card α)

lemma boxMesh_edges_exp (k : ℕ)
    (s : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1)))) :
    (s.card:ℝ)≤exp (log 16*((k:ℝ)+1)*(Fintype.card α:ℝ)) := by
  have hh : (s.card:ℝ)≤(16:ℝ)^((k+1)*Fintype.card α) := by exact_mod_cast boxMesh_edges_card k s
  apply hh.trans_eq
  rw [←exp_log (by norm_num : (0:ℝ)<16),←exp_nat_mul]
  congr 1
  push_cast
  simp only [log_exp]
  ring
end SKGap
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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PowExponentialPair
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
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section SubgaussianMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

lemma pow_le_exponential_pair (x : ℝ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    |x|^k ≤ ((k.factorial : ℝ)/r^k) * (exp (r*x)+exp (-r*x)) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hh := Real.pow_div_factorial_le_exp (r*|x|) (mul_nonneg hr.le (abs_nonneg x)) k
  have he : exp (r*|x|) ≤ exp (r*x)+exp (-r*x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (exp_nonneg _)
    · rw [abs_of_nonpos hx]; have hid : r * -x = -r*x := by ring
      rw [hid]; exact le_add_of_nonneg_left (exp_nonneg _)
  have hg := hh.trans he
  rw [div_le_iff₀ hk,mul_pow] at hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr k)).mpr
  convert hg using 1 <;> ring

lemma subgaussian_abs_moment {r : ℝ} (hr : 0 < r) (hX : HasSubgaussianMGF X c μ) (k : ℕ) :
    (∫ x, |X x|^k ∂μ) ≤
      2*((k.factorial : ℝ)/r^k)*exp ((c : ℝ)*r^2/2) := by
  let C := (k.factorial : ℝ)/r^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : Integrable (fun x => C*(exp (r*X x)+exp (-r*X x))) μ :=
    ((hX.integrable_exp_mul r).add (hX.integrable_exp_mul (-r))).const_mul C
  have hp (x : Ω) : |X x|^k ≤ C*(exp (r*X x)+exp (-r*X x)) := pow_le_exponential_pair (X x) hr k
  have hi : Integrable (fun x => |X x|^k) μ := by
    apply he.mono' (hX.integrable.aestronglyMeasurable.norm.pow k)
    filter_upwards [] with x
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_abs] using hp x
  calc
    _ ≤ ∫ x, C*(exp (r*X x)+exp (-r*X x)) ∂μ := integral_mono hi he hp
    _ = C*(mgf X μ r+mgf X μ (-r)) := by
      rw [integral_const_mul,integral_add (hX.integrable_exp_mul r) (hX.integrable_exp_mul (-r))]
      rfl
    _ ≤ C*(exp ((c:ℝ)*r^2/2)+exp ((c:ℝ)*r^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_sq] using add_le_add (hX.mgf_le r) (hX.mgf_le (-r))
    _ = _ := by dsimp only [C]; ring
end SubgaussianMoments

section GaussianMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_subgaussian_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂stdGaussian E)
      ⟨π^2*(L:ℝ)^2/4,by positivity⟩ (stdGaussian E) where
  integrable_exp_mul r := by
    apply gaussian_integrable_exp_lipschitz (L := L) _ r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  mgf_le r := by
    have hh := stdGaussian_mgf_lipschitz_le hf r
    change (∫ x, exp (r*(f x-∫ y, f y ∂stdGaussian E)) ∂stdGaussian E) ≤ _
    apply hh.trans_eq
    change exp (π^2*r^2*(L:ℝ)^2/8) = exp ((π^2*(L:ℝ)^2/4)*r^2/2)
    congr 1
    ring

lemma stdGaussian_abs_centered_moment {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : 0 < L) (k : ℕ) :
    (∫ x, |f x-∫ y, f y ∂stdGaussian E|^k ∂stdGaussian E) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  have hLr : 0 < (L:ℝ) := hL
  have hh := subgaussian_abs_moment (inv_pos.mpr hLr) (stdGaussian_subgaussian_lipschitz hf) k
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have he : π^2*(L:ℝ)^2/4*((L:ℝ)⁻¹)^2/2 = π^2/8 := by field_simp [ne_of_gt hLr]; ring
  change 2*(k.factorial : ℝ)*exp (π^2/8)*(L:ℝ)^k =
    2*((k.factorial:ℝ)/(L:ℝ)⁻¹^k)*exp ((π^2*(L:ℝ)^2/4)*(L:ℝ)⁻¹^2/2)
  rw [he,inv_pow,div_inv_eq_mul]
  ring
end GaussianMoments
end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductIntegral
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
open MeasureTheory ProbabilityTheory Real
open scoped Topology
section ProductMoments
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integral (F : EuclideanSpace ℝ κ → ℝ) (hF : Continuous F) :
    (∫ g : κ → ℝ, F (WithLp.toLp 2 g) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, F x ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [← map_pi_eq_stdGaussian]
  exact (integral_map (by fun_prop) hF.aestronglyMeasurable).symm

lemma gaussianProduct_integrable_lipschitz {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) :
    Integrable (fun g : κ → ℝ => F (WithLp.toLp 2 g))
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hi := gaussian_integrable_lipschitz (μ := stdGaussian (EuclideanSpace ℝ κ)) hF
  rw [← map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_abs_centered_moment {F : EuclideanSpace ℝ κ → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) (hL : 0 < L) (k : ℕ) :
    (∫ g : κ → ℝ, |F (WithLp.toLp 2 g)-
      ∫ h : κ → ℝ, F (WithLp.toLp 2 h) ∂Measure.pi (fun _ => gaussianReal 0 1)|^k
        ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      (2*(k.factorial : ℝ)*exp (π^2/8))*(L:ℝ)^k := by
  rw [gaussianProduct_integral F hF.continuous]
  rw [gaussianProduct_integral (fun x => |F x-∫ y, F y ∂stdGaussian _|^k) ((hF.continuous.sub continuous_const).abs.pow k)]
  exact stdGaussian_abs_centered_moment hF hL k

end ProductMoments
end SKGap

open MeasureTheory
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
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

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

end SKGap

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

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

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

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_transpose (M*N),Matrix.transpose_mul]
  exact (frobenius_mul_le_opNorm Nᵀ Mᵀ).trans_eq (by rw [opNorm_transpose,Matrix.frobenius_norm_transpose,mul_comm])

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixEntryCLM
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
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixEntry_lipschitz (i k : ι) : LipschitzWith 1 (fun M : Matrix ι ι ℝ => M i k) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul,Matrix.sub_apply] using!
    matrix_entry_le_frobenius (M-N) i k

end SKGap

end
end
end
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

lemma diagonalSeminorm_lipschitz : LipschitzWith 1 (diagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,diagonalSeminorm,←diagonalVector_sub] using!
    (abs_norm_sub_norm_le (diagonalVector M) (diagonalVector N)).trans (diagonalSeminorm_le (M-N))
lemma offDiagonalSeminorm_lipschitz : LipschitzWith 1 (offDiagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  have hh : ‖offDiagonalVector M-offDiagonalVector N‖≤‖M-N‖ := by
    simpa only [←offDiagonalVector_sub,offDiagonalSeminorm] using! offDiagonalSeminorm_le (M-N)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,offDiagonalSeminorm] using!
    (abs_norm_sub_norm_le (offDiagonalVector M) (offDiagonalVector N)).trans hh
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductPower
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {κ : Type*} [Fintype κ]

lemma gaussianProduct_integrable_exp_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (r : ℝ) :
    Integrable (fun g : κ→ℝ=>exp (r*F (WithLp.toLp 2 g))) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  have hi := gaussian_integrable_exp_lipschitz (μ:=stdGaussian (EuclideanSpace ℝ κ)) hF r
  rw [←map_pi_eq_stdGaussian] at hi
  exact hi.comp_measurable (by fun_prop)

lemma gaussianProduct_integrable_abs_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>|F (WithLp.toLp 2 g)|^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  have h1 := gaussianProduct_integrable_exp_lipschitz hF 1
  have h2 := gaussianProduct_integrable_exp_lipschitz hF (-1)
  have hh := (h1.add h2).const_mul (k.factorial:ℝ)
  apply hh.mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).abs.pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simpa only [Real.norm_eq_abs,abs_pow,abs_abs,one_pow,div_one,Pi.add_apply] using
      pow_le_exponential_pair (F (WithLp.toLp 2 g)) (by norm_num : (0:ℝ)<1) k

lemma gaussianProduct_integrable_pow_lipschitz {F : EuclideanSpace ℝ κ→ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (k : ℕ) :
    Integrable (fun g : κ→ℝ=>F (WithLp.toLp 2 g)^k) (Measure.pi (fun _=>gaussianReal 0 1)) := by
  apply (gaussianProduct_integrable_abs_pow_lipschitz hF k).mono'
  · exact ((hF.continuous.comp (by fun_prop : Continuous (WithLp.toLp 2 : (κ→ℝ)→EuclideanSpace ℝ κ))).pow k).aestronglyMeasurable
  · filter_upwards [] with g
    simp only [Real.norm_eq_abs,abs_pow,le_refl]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma matrixCentered_lipschitz {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (matrixCentered F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [matrixCentered,dist_sub_right] using hF.dist_le_mul x y

lemma matrixEntry_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (i k : ι) : LipschitzWith L (fun x=>F x i k) := by
  simpa only [one_mul,Function.comp_def] using (matrixEntry_lipschitz i k).comp hF

lemma diagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>diagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using diagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)
lemma offDiagonalCentered_lip {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) : LipschitzWith L (fun x=>offDiagonalSeminorm (matrixCentered F x)) := by
  simpa only [one_mul,Function.comp_def] using offDiagonalSeminorm_lipschitz.comp (matrixCentered_lipschitz hF)

lemma matrixCentered_even_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (i b : ι) (k : ℕ) :
    (∫ g : κ→ℝ,(matrixCentered F (WithLp.toLp 2 g) i b)^(2*k) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (2*((2*k).factorial:ℝ)*exp (π^2/8))*(L:ℝ)^(2*k) := by
  have hh := gaussianProduct_abs_centered_moment (matrixEntry_lip hF i b) hL (2*k)
  simpa only [matrixCentered,matrixEntryMean,Matrix.sub_apply,pow_mul,sq_abs] using hh

lemma diagonalCentered_second_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^2 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)*(4*exp (π^2/8))*(L:ℝ)^2 := by
  simp_rw [diagonalSeminorm_sq]
  rw [integral_finsetSum _ (fun i _=>gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) i i) 2)]
  apply (Finset.sum_le_sum (fun i _=>matrixCentered_even_moment hF hL i i 1)).trans_eq
  norm_num [Finset.sum_const,mul_assoc]

lemma offDiagonalCentered_fourth_moment {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g))^4 ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      (Fintype.card ι:ℝ)^2*(48*exp (π^2/8))*(L:ℝ)^4 := by
  simp_rw [offDiagonalSeminorm_fourth]
  have hi (p : ι×ι) : Integrable (fun g : κ→ℝ=>if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      (Measure.pi (fun _=>gaussianReal 0 1)) := by
    split_ifs
    · exact integrable_const _
    · exact gaussianProduct_integrable_pow_lipschitz (matrixEntry_lip (matrixCentered_lipschitz hF) p.1 p.2) 4
  rw [integral_finsetSum _ (fun p _=>hi p)]
  have hb (p : ι×ι) : (∫ g : κ→ℝ,(if p.1=p.2 then 0 else matrixCentered F (WithLp.toLp 2 g) p.1 p.2^4)
      ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤ (48*exp (π^2/8))*(L:ℝ)^4 := by
    split_ifs
    · simp only [integral_zero];positivity
    · have hh := matrixCentered_even_moment hF hL p.1 p.2 2
      norm_num at hh
      exact hh
  apply (Finset.sum_le_sum (fun p _=>hb p)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

lemma gaussianProduct_jensen_pow {F : EuclideanSpace ℝ κ→ℝ} {L : NNReal}
    (hF : LipschitzWith L F) (hpos : ∀ x,0≤F x) (k : ℕ) :
    (∫ g : κ→ℝ,F (WithLp.toLp 2 g) ∂Measure.pi (fun _=>gaussianReal 0 1))^k≤
      ∫ g : κ→ℝ,F (WithLp.toLp 2 g)^k ∂Measure.pi (fun _=>gaussianReal 0 1) := by
  exact (convexOn_pow (𝕜:=ℝ) k).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun g=>hpos (WithLp.toLp 2 g))) (gaussianProduct_integrable_lipschitz hF)
    (gaussianProduct_integrable_pow_lipschitz hF k)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma matrixNormConstant_bounds : 1≤ matrixNormConstant ∧
    4*exp (π^2/8)≤ matrixNormConstant^2 ∧ 48*exp (π^2/8)≤ matrixNormConstant^4 := by
  have hE := (exp_pos (π^2/8)).le
  have hC : 1≤ matrixNormConstant := by unfold matrixNormConstant;linarith
  have hC2 : matrixNormConstant≤ matrixNormConstant^2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤2)
  have hC4 : matrixNormConstant≤ matrixNormConstant^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (by decide : 1≤4)
  refine ⟨hC,?_,?_⟩ <;> unfold matrixNormConstant at * <;> linarith

lemma gaussianProduct_centered_matrix_norms {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) :
    (∫ g : κ→ℝ,diagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) ∧
    (∫ g : κ→ℝ,offDiagonalSeminorm (matrixCentered F (WithLp.toLp 2 g)) ∂Measure.pi (fun _=>gaussianReal 0 1))≤
      matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hC0 : 0≤ matrixNormConstant := zero_le_one.trans matrixNormConstant_bounds.1
  have hcn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  constructor
  · apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (diagonalCentered_lip hF) (fun x=>norm_nonneg (diagonalVector (matrixCentered F x))) 2
    apply (hJ.trans (diagonalCentered_second_moment hF hL)).trans
    rw [mul_pow,mul_pow,sq_sqrt hcn]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.1 hcn) (sq_nonneg (L:ℝ))
    nlinarith only [hh]
  · apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity)
    have hJ := gaussianProduct_jensen_pow (offDiagonalCentered_lip hF) (fun x=>norm_nonneg (offDiagonalVector (matrixCentered F x))) 4
    apply (hJ.trans (offDiagonalCentered_fourth_moment hF hL)).trans
    have hs : sqrt (Fintype.card ι)^4=(Fintype.card ι:ℝ)^2 := by
      calc
        _ = (sqrt (Fintype.card ι)^2)^2 := by ring
        _ = _ := by rw [sq_sqrt hcn]
    rw [mul_pow,mul_pow,hs]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left matrixNormConstant_bounds.2.2 (sq_nonneg (Fintype.card ι:ℝ))) (by positivity : (0:ℝ)≤(L:ℝ)^4)
    nlinarith only [hh]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpDuhamel
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
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
namespace SKGap
section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

lemma exp_duhamel (a b : A) :
    exp a - exp b = ∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => exp ((1-u) • a) * exp (u • b))
      (-(exp ((1-u) • a) * (a-b) * exp (u • b))) u := by
    have h₁ := (hasDerivAt_exp_smul_const a (1-u)).scomp u ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u))
    have h₂ := hasDerivAt_exp_smul_const' b u
    convert h₁.mul h₂ using 1 <;> (try simp only [zero_sub, neg_smul, one_smul]) <;> noncomm_ring
  have hc : Continuous (fun u : ℝ => -(exp ((1-u) • a) * (a-b) * exp (u • b))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_neg, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    sub_zero, one_smul, mul_one, neg_neg, neg_sub] using congrArg Neg.neg hh.symm

end Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]
  [StarRing A] [ContinuousStar A] [CStarRing A]

omit [CStarRing A] in
lemma exp_skew_unitary (a : A) (ha : star a = -a) (t : ℝ)
    [StarModule ℝ A] : exp (t • a) ∈ unitary A := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change star (t • a) = -(t • a)
  simp [ha]

lemma exp_skew_difference [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) : ‖exp a - exp b‖ ≤ ‖a-b‖ := by
  rw [exp_duhamel]
  have hc : Continuous (fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)) := by fun_prop
  have hh : ∀ u : ℝ, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ = ‖a-b‖ := by
    intro u
    rw [CStarRing.norm_mul_coe_unitary _ ⟨_,exp_skew_unitary b hb u⟩,
      CStarRing.norm_coe_unitary_mul ⟨_,exp_skew_unitary a ha (1-u)⟩]
  calc
    ‖∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b)‖ ≤
        ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖a-b‖ := by simp only [hh]; simp

end SKGap

open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap
namespace ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := (lin M).le_opNorm (colVec N k)
  change ‖lin M (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh,norm_nonneg (lin M (colVec N k)),mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_adjoint (M : Matrix ι ι ℂ) : opNorm Mᴴ = opNorm M := by
  rw [opNorm,lin_adjoint,ContinuousLinearMap.adjoint.norm_map]
  rfl

lemma frobenius_mul_le_opNorm_right (M N : Matrix ι ι ℂ) : ‖M*N‖ ≤ ‖M‖ * opNorm N := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*N),Matrix.conjTranspose_mul]
  exact (frobenius_mul_le_opNorm Nᴴ Mᴴ).trans_eq (by rw [opNorm_adjoint,Matrix.frobenius_norm_conjTranspose,mul_comm])

end ComplexMatrix
end SKGap

namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lin_exp (M : Matrix ι ι ℂ) : lin (NormedSpace.exp M) = NormedSpace.exp (lin M) :=
  NormedSpace.map_exp linHom continuous_lin M

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LinSub
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
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lin_sub (M N : Matrix ι ι ℂ) : lin (M-N) = lin M - lin N := linEquiv.map_sub M N
lemma lin_neg (M : Matrix ι ι ℂ) : lin (-M) = - lin M := linEquiv.map_neg M
lemma opNorm_smul (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (t • M) = |t| * opNorm M := by
  change ‖lin (t • M)‖ = _
  have hh : lin (t • M) = t • lin M := by ext x i; simp [lin,Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.smul_mulVec]
  rw [hh,norm_smul,Real.norm_eq_abs]
  rfl

lemma unitary_exp_smul (M : Matrix ι ι ℂ) (hM : Mᴴ = -M) (u : ℝ) :
    exp (u • M) ∈ unitary (Matrix ι ι ℂ) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change (u • M)ᴴ = -(u • M)
  simp [hM]

lemma opNorm_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    opNorm (exp M-exp N) ≤ opNorm (M-N) := by
  have hMl : star (lin M) = -lin M := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hM,lin_neg]
  have hNl : star (lin N) = -lin N := by rw [ContinuousLinearMap.star_eq_adjoint,← lin_adjoint,hN,lin_neg]
  let : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := .restrictScalars ℚ ℝ _
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := SKGap.exp_skew_difference (lin M) (lin N) hMl hNl
  simpa only [opNorm,lin_sub,lin_exp] using hh

lemma frobenius_exp_sub (M N : Matrix ι ι ℂ) (hM : Mᴴ = -M) (hN : Nᴴ = -N) :
    ‖exp M-exp N‖ ≤ ‖M-N‖ := by
  rw [show exp M-exp N = _ from SKGap.exp_duhamel M N]
  have hh (u : ℝ) : ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ = ‖M-N‖ := by
    rw [frobenius_mul_unitary _ _ (unitary_exp_smul N hN u),
      frobenius_unitary_mul _ _ (unitary_exp_smul M hM (1-u))]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • M) * (M-N) * exp (u • N)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖M-N‖ := by simp only [hh]; simp

lemma exp_four_point (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d) :
    ‖(exp a-exp b)-(exp c-exp d)‖ ≤
      ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun a b : Matrix ι ι ℂ => fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)
  have hF (a b : Matrix ι ι ℂ) : Continuous (F a b) := by dsimp [F]; fun_prop
  have hbound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖F a b u-F c d u‖ ≤ ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
    have hsa : ((1-u) • a)ᴴ = -((1-u) • a) := by simp [ha]
    have hsc : ((1-u) • c)ᴴ = -((1-u) • c) := by simp [hc]
    have hsb : (u • b)ᴴ = -(u • b) := by simp [hb]
    have hsd : (u • d)ᴴ = -(u • d) := by simp [hd]
    have h₁ := opNorm_exp_sub ((1-u) • a) ((1-u) • c) hsa hsc
    have h₂ := opNorm_exp_sub (u • b) (u • d) hsb hsd
    rw [← smul_sub,opNorm_smul,abs_of_nonneg (sub_nonneg.mpr hu.2)] at h₁
    rw [← smul_sub,opNorm_smul,abs_of_nonneg hu.1] at h₂
    have ha0 : 0 ≤ opNorm (a-c) := norm_nonneg _
    have hb0 : 0 ≤ opNorm (b-d) := norm_nonneg _
    have h₁' : opNorm (exp ((1-u) • a)-exp ((1-u) • c)) ≤ opNorm (a-c) := by nlinarith [hu.1]
    have h₂' : opNorm (exp (u • b)-exp (u • d)) ≤ opNorm (b-d) := by nlinarith [hu.2]
    have hid : F a b u-F c d u =
        exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b) +
        (exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b) +
        exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d)) := by dsimp [F]; noncomm_ring
    rw [hid]
    have hfirst : ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ = ‖(a-b)-(c-d)‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u),
        frobenius_unitary_mul _ _ (unitary_exp_smul a ha (1-u))]
    have hsecond : ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ ≤ opNorm (a-c)*‖c-d‖ := by
      rw [frobenius_mul_unitary _ _ (unitary_exp_smul b hb u)]
      exact (frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₁' (norm_nonneg _))
    have hthird : ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ ≤ opNorm (b-d)*‖c-d‖ := by
      rw [mul_assoc,frobenius_unitary_mul _ _ (unitary_exp_smul c hc (1-u))]
      exact (frobenius_mul_le_opNorm_right _ _).trans (by nlinarith [norm_nonneg (c-d)])
    calc
      _ ≤ ‖exp ((1-u) • a)*((a-b)-(c-d))*exp (u • b)‖ +
        ‖(exp ((1-u) • a)-exp ((1-u) • c))*(c-d)*exp (u • b)‖ +
        ‖exp ((1-u) • c)*(c-d)*(exp (u • b)-exp (u • d))‖ := norm_add₃_le
      _ ≤ _ := by rw [hfirst]; nlinarith
  rw [show exp a-exp b = _ from SKGap.exp_duhamel a b, show exp c-exp d = _ from SKGap.exp_duhamel c d]
  change ‖(∫ u : ℝ in (0 : ℝ)..1, F a b u)-(∫ u : ℝ in (0 : ℝ)..1, F c d u)‖ ≤ _
  rw [← intervalIntegral.integral_sub ((hF a b).intervalIntegrable 0 1) ((hF c d).intervalIntegrable 0 1)]
  calc
    _ ≤ ∫ u : ℝ in (0 : ℝ)..1, ‖F a b u-F c d u‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ : ℝ in (0 : ℝ)..1, ‖(a-b)-(c-d)‖ + (opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num) (((hF a b).sub (hF c d)).norm.intervalIntegrable 0 1)
        (intervalIntegrable_const)
      exact hbound
    _ = _ := by simp

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instPseudoMetrizableSpaceMatrixComplex_solutions : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma lin_csmul (z : ℂ) (M : Matrix ι ι ℂ) : lin (z • M) = z • lin M :=
  (linEquiv (ι := ι)).map_smul z M

lemma opNorm_csmul (z : ℂ) (M : Matrix ι ι ℂ) : opNorm (z • M) = ‖z‖ * opNorm M := by
  simp only [opNorm,lin_csmul,norm_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_skew (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    (imaginary t M)ᴴ = -(imaginary t M) := by
  simp [imaginary,Matrix.conjTranspose_smul,hM,star_mul,mul_comm]

lemma imaginary_norm (t : ℝ) (M : Matrix ι ι ℂ) : ‖imaginary t M‖ = |t| * ‖M‖ := by
  simp [imaginary,norm_smul]

lemma imaginary_opNorm (t : ℝ) (M : Matrix ι ι ℂ) : opNorm (imaginary t M) = |t| * opNorm M := by
  simp [imaginary,opNorm_csmul]

omit [Fintype ι] [DecidableEq ι] in
lemma imaginary_sub (t : ℝ) (M N : Matrix ι ι ℂ) :
    imaginary t (M-N) = imaginary t M-imaginary t N := by simp [imaginary,smul_sub]

lemma imaginary_exp_unitary (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    exp (imaginary t M) ∈ unitary (Matrix ι ι ℂ) := by
  simpa using unitary_exp_smul _ (imaginary_skew t M hM) 1

lemma imaginary_exp_norm (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    ‖exp (imaginary t M)‖ = ‖(1 : Matrix ι ι ℂ)‖ := by
  simpa using frobenius_unitary_mul (exp (imaginary t M)) 1 (imaginary_exp_unitary t M hM)

lemma imaginary_exp_opNorm_le (t : ℝ) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (exp (imaginary t M)) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary _ (imaginary_exp_unitary t M hM))]
  simp

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions
lemma kernel_integrable {g : ℝ → ℂ} (hg : Integrable g) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    Integrable (fun t : ℝ => g t • exp (imaginary t M)) := by
  have hc : Continuous (fun t : ℝ => exp (imaginary t M)) := by dsimp [imaginary]; fun_prop
  apply (hg.norm.mul_const ‖(1 : Matrix ι ι ℂ)‖).mono' (hg.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖g t • exp (imaginary t M)‖ ≤ _
  rw [norm_smul,imaginary_exp_norm t M hM]

lemma kernelMatrix_lipschitz {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖kernelMatrix g M-kernelMatrix g N‖ ≤ (∫ t : ℝ, ‖g t‖*|t|) * ‖M-N‖ := by
  rw [kernelMatrix,kernelMatrix,← integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)]
  calc
    _ ≤ ∫ t : ℝ, ‖g t • exp (imaginary t M)-g t • exp (imaginary t N)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖M-N‖ := by
      apply integral_mono ((kernel_integrable hg M hM).sub (kernel_integrable hg N hN)).norm (hg₁.mul_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← smul_sub,norm_smul]
      have hh := frobenius_exp_sub _ _ (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_norm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    _ = _ := integral_mul_const _ _

lemma kernelMatrix_four_point {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (hg₂ : Integrable (fun t : ℝ => ‖g t‖*|t|^2))
    (a b c d : Matrix ι ι ℂ) (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(kernelMatrix g a-kernelMatrix g b)-(kernelMatrix g c-kernelMatrix g d)‖ ≤
      (∫ t : ℝ, ‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
      (∫ t : ℝ, ‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  let F := fun (M : Matrix ι ι ℂ) (t : ℝ) => g t • exp (imaginary t M)
  have hi (M : Matrix ι ι ℂ) (hM : Mᴴ = M) : Integrable (F M) := kernel_integrable hg M hM
  have hi' := ((hi a ha).sub (hi b hb)).sub ((hi c hc).sub (hi d hd))
  change ‖((∫ t, F a t)-(∫ t, F b t))-((∫ t, F c t)-(∫ t, F d t))‖ ≤ _
  rw [← integral_sub (hi a ha) (hi b hb),← integral_sub (hi c hc) (hi d hd),
    ← integral_sub (f := fun t => F a t-F b t) (g := fun t => F c t-F d t)
      ((hi a ha).sub (hi b hb)) ((hi c hc).sub (hi d hd))]
  calc
    _ ≤ ∫ t : ℝ, ‖(F a t-F b t)-(F c t-F d t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*‖(a-b)-(c-d)‖ +
        (‖g t‖*|t|^2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
      apply integral_mono hi'.norm ((hg₁.mul_const _).add ((hg₂.mul_const _).mul_const _))
      intro t
      dsimp only [F,Pi.sub_apply]
      rw [← smul_sub,← smul_sub,← smul_sub,norm_smul]
      have hh := exp_four_point (imaginary t a) (imaginary t b) (imaginary t c) (imaginary t d)
        (imaginary_skew t a ha) (imaginary_skew t b hb) (imaginary_skew t c hc) (imaginary_skew t d hd)
      simp only [← imaginary_sub,imaginary_norm,imaginary_opNorm] at hh
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by dsimp only [Pi.add_apply]; ring)
    _ = _ := by rw [integral_add (hg₁.mul_const _) ((hg₂.mul_const _).mul_const _)]; simp only [integral_mul_const]

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EntryLM
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
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_kernelMatrix {g : ℝ → ℂ} (hg : Integrable g)
    (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (kernelMatrix g M) ≤ ∫ t : ℝ, ‖g t‖ := by
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hi := linCLM.integral_comp_comm (kernel_integrable hg M hM)
  change ‖linCLM (∫ t : ℝ, g t • exp (imaginary t M))‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (g t • exp (imaginary t M))‖ := congrArg norm hi.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (g t • exp (imaginary t M))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖g t‖ := by
      apply integral_mono (linCLM.integrable_comp (kernel_integrable hg M hM)).norm hg.norm
      intro t
      change ‖lin (g t • exp (imaginary t M))‖ ≤ _
      rw [lin_csmul,norm_smul]
      exact (mul_le_mul_of_nonneg_left (imaginary_exp_opNorm_le t M hM) (norm_nonneg _)).trans_eq (mul_one _)

lemma schwartzMatrix_opNorm (f : 𝓢(ℝ,ℂ)) (M : Matrix ι ι ℂ) (hM : Mᴴ = M) :
    opNorm (schwartzMatrix f M) ≤ ∫ t : ℝ, ‖(𝓕 f) t‖ :=
  opNorm_kernelMatrix (𝓕 f).integrable _ (by simp [hM])

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_FourierMoment
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
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fourierMoment_integrable (f : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|^k) := by
  simpa only [Real.norm_eq_abs,mul_comm] using (𝓕 f).integrable_pow_mul volume k

lemma opNorm_rsmul (r : ℝ) (M : Matrix ι ι ℂ) : opNorm (r • M) = |r| * opNorm M := by
  change opNorm ((r:ℂ) • M) = _
  rw [opNorm_csmul,Complex.norm_real,Real.norm_eq_abs]

lemma schwartzMatrix_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f M-schwartzMatrix f N‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖M-N‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_lipschitz (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

lemma schwartzMatrix_four_point (f : 𝓢(ℝ,ℂ)) (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(schwartzMatrix f a-schwartzMatrix f b)-(schwartzMatrix f c-schwartzMatrix f d)‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖(a-b)-(c-d)‖ +
      ((2*Real.pi)^2*fourierMoment f 2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_four_point (𝓕 f).integrable hf₁ (fourierMoment_integrable f 2)
    ((2*Real.pi:ℝ) • a) ((2*Real.pi:ℝ) • b) ((2*Real.pi:ℝ) • c) ((2*Real.pi:ℝ) • d)
    (by simp [ha]) (by simp [hb]) (by simp [hc]) (by simp [hd])
  simp only [← smul_sub,norm_smul,opNorm_rsmul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormKernelMatrixSub
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
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_3
local instance instPseudoMetrizableSpaceMatrixComplex_solutions_3_r9cbbd2_1 : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))
lemma opNorm_kernelMatrix_sub {g : ℝ → ℂ} (hg : Integrable g)
    (hg₁ : Integrable (fun t : ℝ => ‖g t‖*|t|))
    (M N : Matrix ι ι ℂ) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (kernelMatrix g M-kernelMatrix g N) ≤
      (∫ t : ℝ, ‖g t‖*|t|)*opNorm (M-N) := by
  let F := fun t : ℝ => g t • exp (imaginary t M)-g t • exp (imaginary t N)
  have hi : Integrable F := (kernel_integrable hg M hM).sub (kernel_integrable hg N hN)
  let : CompleteSpace (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    ContinuousLinearMap.instCompleteSpace
  have hh := linCLM.integral_comp_comm hi
  have he : kernelMatrix g M-kernelMatrix g N = ∫ t : ℝ, F t := by
    exact (integral_sub (kernel_integrable hg M hM) (kernel_integrable hg N hN)).symm
  rw [he]
  change ‖linCLM (∫ t : ℝ, F t)‖ ≤ _
  calc
    _ = ‖∫ t : ℝ, linCLM (F t)‖ := congrArg norm hh.symm
    _ ≤ ∫ t : ℝ, ‖linCLM (F t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖g t‖*|t|)*opNorm (M-N) := by
      apply integral_mono (linCLM.integrable_comp hi).norm (hg₁.mul_const _)
      intro t
      have hb := opNorm_exp_sub (imaginary t M) (imaginary t N) (imaginary_skew t M hM) (imaginary_skew t N hN)
      rw [← imaginary_sub,imaginary_opNorm] at hb
      change opNorm (F t) ≤ _
      dsimp only [F]
      rw [← smul_sub,opNorm_csmul]
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_mul_const _ _

lemma schwartzMatrix_opNorm_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    opNorm (schwartzMatrix f M-schwartzMatrix f N) ≤
      (2*Real.pi*fourierMoment f 1)*opNorm (M-N) := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := opNorm_kernelMatrix_sub (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,opNorm_smul,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ opNorm M := norm_nonneg _
lemma opNorm_add (M N : Matrix ι ι ℂ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  change ‖linEquiv (M+N)‖ ≤ _
  rw [(linEquiv (ι := ι)).map_add]
  exact norm_add_le _ _
lemma opNorm_sub (M N : Matrix ι ι ℂ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖lin (M-N)‖ ≤ _
  have hh : lin (M-N) = lin M-lin N := linEquiv.map_sub M N
  rw [hh]
  exact norm_sub_le _ _
lemma opNorm_mul (M N : Matrix ι ι ℂ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  change ‖lin (M*N)‖ ≤ _
  rw [lin_mul]
  exact norm_mul_le _ _
lemma opNorm_neg (M : Matrix ι ι ℂ) : opNorm (-M) = opNorm M := by
  change ‖lin (-M)‖ = _
  have hh : lin (-M) = -lin M := linEquiv.map_neg M
  rw [hh,norm_neg]
  rfl
lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℂ) ≤ 1 := by
  rw [opNorm,lin_one]
  exact ContinuousLinearMap.norm_id_le

lemma sandwich_frobenius (D E : Matrix ι ι ℂ) :
    ‖D*E*D‖ ≤ opNorm D^2*‖E‖ := by
  calc
    _ ≤ ‖D*E‖*opNorm D := frobenius_mul_le_opNorm_right _ _
    _ ≤ (opNorm D*‖E‖)*opNorm D := mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_opNorm (D E : Matrix ι ι ℂ) :
    opNorm (D*E*D) ≤ opNorm D^2*opNorm E := by
  calc
    _ ≤ opNorm (D*E)*opNorm D := opNorm_mul _ _
    _ ≤ (opNorm D*opNorm E)*opNorm D := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _)
    _ = _ := by ring

lemma sandwich_difference_frobenius (D D' E : Matrix ι ι ℂ) :
    ‖D*E*D-D'*E*D'‖ ≤ (opNorm D+opNorm D')*opNorm (D-D')*‖E‖ := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(D-D')*E*D‖+‖D'*E*(D-D')‖ := norm_add_le _ _
    _ ≤ (opNorm (D-D')*‖E‖)*opNorm D+(opNorm D'*‖E‖)*opNorm (D-D') := by
      apply add_le_add
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
      · exact (frobenius_mul_le_opNorm_right _ _).trans
          (mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma sandwich_difference_opNorm (D D' E : Matrix ι ι ℂ) :
    opNorm (D*E*D-D'*E*D') ≤ (opNorm D+opNorm D')*opNorm (D-D')*opNorm E := by
  have he : D*E*D-D'*E*D' = (D-D')*E*D+D'*E*(D-D') := by noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm ((D-D')*E*D)+opNorm (D'*E*(D-D')) := opNorm_add _ _
    _ ≤ (opNorm (D-D')*opNorm E)*opNorm D+(opNorm D'*opNorm E)*opNorm (D-D') := by
      apply add_le_add
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
      · exact (opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (opNorm_mul _ _) (opNorm_nonneg _))
    _ = _ := by ring

lemma product_four_point (a b c d e f g h : Matrix ι ι ℂ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e + ‖c-d‖*opNorm (e-g) +
      opNorm (b-d)*‖e-f‖ + opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h) =
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShift
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
namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_sub (B D M N : Matrix ι ι ℂ) :
    sandShift B D M-sandShift B D N = -(D*(M-N)*D) := by dsimp [sandShift]; noncomm_ring

lemma sandShift_lipschitz (B D M N : Matrix ι ι ℂ) :
    ‖sandShift B D M-sandShift B D N‖ ≤ opNorm D^2*‖M-N‖ := by
  rw [sandShift_sub,norm_neg]
  exact sandwich_frobenius _ _

lemma sandShift_parameter (B B' D D' M : Matrix ι ι ℂ) :
    opNorm (sandShift B D M-sandShift B' D' M) ≤
      opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*opNorm M := by
  have he : sandShift B D M-sandShift B' D' M = (B-B')-(D*M*D-D'*M*D') := by dsimp [sandShift]; abel
  rw [he]
  calc
    _ ≤ opNorm (B-B')+opNorm (D*M*D-D'*M*D') := opNorm_sub (B-B') (D*M*D-D'*M*D')
    _ ≤ _ := by
      have hh := sandwich_difference_opNorm D D' M
      linarith only [hh]

lemma sandShift_four_point (B B' D D' M N : Matrix ι ι ℂ) :
    ‖(sandShift B D M-sandShift B D N)-(sandShift B' D' M-sandShift B' D' N)‖ ≤
      (opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖ := by
  rw [sandShift_sub,sandShift_sub,← norm_neg]
  have he : -(-(D*(M-N)*D)- -(D'*(M-N)*D')) = D*(M-N)*D-D'*(M-N)*D' := by abel
  rw [he]
  exact sandwich_difference_frobenius _ _ _

lemma schwartzMatrix_sandShift_lipschitz (f : 𝓢(ℝ,ℂ)) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N)‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖ := by
  exact (schwartzMatrix_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hM)
    (sandShift_hermitian _ _ _ hB hD hN)).trans
    ((mul_le_mul_of_nonneg_left (sandShift_lipschitz B D M N)
      (by positivity [fourierMoment_nonneg f 1])).trans_eq (by ring))

lemma schwartzMatrix_sandShift_four_point (f : 𝓢(ℝ,ℂ)) (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D')
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖(schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N))-
      (schwartzMatrix f (sandShift B' D' M)-schwartzMatrix f (sandShift B' D' N))‖ ≤
      ((2*Real.pi*fourierMoment f 1)*(opNorm D+opNorm D')*opNorm (D-D')+
        ((2*Real.pi)^2*fourierMoment f 2)*
          (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*opNorm D'^2)*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hQ : 0 ≤ (2*Real.pi)^2*fourierMoment f 2 := by have := fourierMoment_nonneg f 2; positivity
  have hP : 0 ≤ (opNorm D+opNorm D')*opNorm (D-D') :=
    mul_nonneg (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) (opNorm_nonneg _)
  have hp := add_le_add (sandShift_parameter B B' D D' M) (sandShift_parameter B B' D D' N)
  have hp' : opNorm (sandShift B D M-sandShift B' D' M)+opNorm (sandShift B D N-sandShift B' D' N) ≤
      2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N) := by nlinarith only [hp]
  have hx := schwartzMatrix_four_point f (sandShift B D M) (sandShift B D N) (sandShift B' D' M) (sandShift B' D' N)
    (sandShift_hermitian _ _ _ hB hD hM) (sandShift_hermitian _ _ _ hB hD hN)
    (sandShift_hermitian _ _ _ hB' hD' hM) (sandShift_hermitian _ _ _ hB' hD' hN)
  apply hx.trans
  calc
    _ ≤ (2*Real.pi*fourierMoment f 1)*((opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖)+
      ((2*Real.pi)^2*fourierMoment f 2)*
        (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*(opNorm D'^2*‖M-N‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sandShift_four_point _ _ _ _ _ _) hL
      · apply mul_le_mul (mul_le_mul_of_nonneg_left hp' hQ) (sandShift_lipschitz B' D' M N) (norm_nonneg _)
        exact mul_nonneg hQ (add_nonneg (mul_nonneg (by norm_num) (opNorm_nonneg _))
          (mul_nonneg hP (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _))))
    _ = _ := by ring

end SKGap.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology
namespace SKGap
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexProject_mem {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    convexProject hK x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).1

lemma convexProject_minimal {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    ‖x-convexProject hK x‖ = ⨅ y : K, ‖x-y‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).2

lemma convexProject_inner {K : Set E} (hK : ClosedConvexNonempty K) (x : E)
    {y : E} (hy : y ∈ K) :
    inner ℝ (x-convexProject hK x) (y-convexProject hK x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero hK.convex (convexProject_mem hK x)).mp
    (convexProject_minimal hK x)) y hy

lemma convexProject_lipschitz {K : Set E} (hK : ClosedConvexNonempty K) :
    LipschitzWith 1 (convexProject hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  let p := convexProject hK x
  let q := convexProject hK y
  have hx := convexProject_inner hK x (convexProject_mem hK y)
  have hy := convexProject_inner hK y (convexProject_mem hK x)
  change inner ℝ (x-p) (q-p) ≤ 0 at hx
  change inner ℝ (y-q) (p-q) ≤ 0 at hy
  have hi : ‖p-q‖^2 ≤ inner ℝ (p-q) (x-y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_comm] at *
    nlinarith
  have hb := real_inner_le_norm (p-q) (x-y)
  nlinarith [norm_nonneg (p-q),norm_nonneg (x-y)]

end Projection
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

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Vectorize
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
namespace SKGap.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith 1 (matrixProject (ι := ι) R hR) :=
  SKGap.convexProject_lipschitz _

lemma matrixProject_bound (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ) :
    (matrixProject R hR M)ᴴ = matrixProject R hR M ∧ opNorm (matrixProject R hR M) ≤ R :=
  SKGap.convexProject_mem (hermitianBall_good (ι := ι) hR) M

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixProject_sub_norm (R : ℝ) (hR : 0 ≤ R) (M N : Matrix ι ι ℂ) :
    ‖matrixProject R hR M-matrixProject R hR N‖ ≤ ‖M-N‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (matrixProject_lipschitz R hR).dist_le_mul M N

lemma truncatedG_opNorm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedG f R hR B D M) ≤ opNorm D^2*fourierMoment f 0 := by
  have hS := sandShift_hermitian B D (matrixProject R hR M) hB hD (matrixProject_bound R hR M).1
  apply (sandwich_opNorm D _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [fourierMoment,pow_zero,mul_one] using schwartzMatrix_opNorm f _ hS

lemma truncatedG_sub_norm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedG f R hR B D M-truncatedG f R hR B D N‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^4*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hM := (matrixProject_bound R hR M).1
  have hN := (matrixProject_bound R hR N).1
  have hl := schwartzMatrix_sandShift_lipschitz f B D (matrixProject R hR M) (matrixProject R hR N) hB hD hM hN
  have he : truncatedG f R hR B D M-truncatedG f R hR B D N =
      D*(schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N)))*D := by dsimp [truncatedG]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm D^2*‖schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N))‖ := sandwich_frobenius _ _
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖matrixProject R hR M-matrixProject R hR N‖) :=
      mul_le_mul_of_nonneg_left hl (sq_nonneg _)
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖) := by
      gcongr
      exact matrixProject_sub_norm _ _ _ _
    _ = _ := by ring

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonalChange_nonneg (D D' : Matrix ι ι ℂ) : 0 ≤ diagonalChange D D' := by
  unfold diagonalChange
  positivity [opNorm_nonneg D,opNorm_nonneg D',opNorm_nonneg (D-D')]
lemma shiftChange_nonneg {R : ℝ} (hR : 0 ≤ R) (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ shiftChange R B B' D D' := by
  unfold shiftChange
  positivity [opNorm_nonneg (B-B'),diagonalChange_nonneg D D']
lemma g_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ gBound f D ∧ 0 ≤ gLip f D ∧ 0 ≤ gChange f R B B' D D' ∧ 0 ≤ gMixed f R B B' D D' := by
  have h₀ := fourierMoment_nonneg f 0
  have h₁ := (fl_nonneg f).1
  have h₂ := (fl_nonneg f).2
  have hd := diagonalChange_nonneg D D'
  have hs := shiftChange_nonneg hR B B' D D'
  unfold gBound gLip gChange gMixed
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma truncatedG_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    opNorm (truncatedG f R hR B D M-truncatedG f R hR B' D' M) ≤
      gChange f R B B' D D' := by
  let P := matrixProject R hR M
  let F := schwartzMatrix f (sandShift B D P)
  let F' := schwartzMatrix f (sandShift B' D' P)
  have hP := matrixProject_bound R hR M
  have hF : opNorm F ≤ fourierMoment f 0 := by
    simpa only [F,fourierMoment,pow_zero,mul_one] using
      schwartzMatrix_opNorm f _ (sandShift_hermitian _ _ _ hB hD hP.1)
  have hs : opNorm (sandShift B D P-sandShift B' D' P) ≤ shiftChange R B B' D D' := by
    apply (sandShift_parameter B B' D D' P).trans
    unfold shiftChange diagonalChange
    exact add_le_add_right (mul_le_mul_of_nonneg_left hP.2 (diagonalChange_nonneg D D')) _
  have hL : opNorm (F-F') ≤ fl1 f*shiftChange R B B' D D' :=
    (schwartzMatrix_opNorm_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hP.1)
      (sandShift_hermitian _ _ _ hB' hD' hP.1)).trans
      (mul_le_mul_of_nonneg_left hs (fl_nonneg f).1)
  have he : truncatedG f R hR B D M-truncatedG f R hR B' D' M =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm (D*F*D-D'*F*D')+opNorm (D'*(F-F')*D') := opNorm_add _ _
    _ ≤ diagonalChange D D'*opNorm F+opNorm D'^2*opNorm (F-F') :=
      add_le_add (sandwich_difference_opNorm _ _ _) (sandwich_opNorm _ _)
    _ ≤ diagonalChange D D'*fourierMoment f 0+opNorm D'^2*(fl1 f*shiftChange R B B' D D') :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hL (sq_nonneg _))
    _ = _ := by unfold gChange; ring

lemma truncatedG_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N)‖ ≤
      gMixed f R B B' D D'*‖M-N‖ := by
  let P := matrixProject R hR M
  let Q := matrixProject R hR N
  let F := schwartzMatrix f (sandShift B D P)-schwartzMatrix f (sandShift B D Q)
  let F' := schwartzMatrix f (sandShift B' D' P)-schwartzMatrix f (sandShift B' D' Q)
  have hP := matrixProject_bound R hR M
  have hQ := matrixProject_bound R hR N
  have hPQ : ‖P-Q‖ ≤ ‖M-N‖ := matrixProject_sub_norm _ _ _ _
  have hF : ‖F‖ ≤ fl1 f*opNorm D^2*‖M-N‖ :=
    (schwartzMatrix_sandShift_lipschitz f B D P Q hB hD hP.1 hQ.1).trans
      (mul_le_mul_of_nonneg_left hPQ (mul_nonneg (fl_nonneg f).1 (sq_nonneg _)))
  have hFF : ‖F-F'‖ ≤
      (fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖ := by
    apply (schwartzMatrix_sandShift_four_point f B B' D D' P Q hB hB' hD hD' hP.1 hQ.1).trans
    simp only [mul_assoc (2*Real.pi*fourierMoment f 1) (opNorm D+opNorm D')]
    change (fl1 f*diagonalChange D D'+fl2 f*
      (2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q))*opNorm D'^2)*‖P-Q‖ ≤ _
    have hd := diagonalChange_nonneg D D'
    have hs := shiftChange_nonneg hR B B' D D'
    have hc : 2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q) ≤
        2*shiftChange R B B' D D' := by
      calc
        _ ≤ 2*opNorm (B-B')+diagonalChange D D'*(R+R) :=
          add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hP.2 hQ.2) hd) _
        _ = _ := by unfold shiftChange; ring
    have hc' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (fl_nonneg f).2) (sq_nonneg (opNorm D'))
    have hcoef := add_le_add_right hc' (fl1 f*diagonalChange D D')
    have hn : 0 ≤ fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2 :=
      add_nonneg (mul_nonneg (fl_nonneg f).1 hd)
        (mul_nonneg (mul_nonneg (fl_nonneg f).2 (mul_nonneg (by norm_num) hs)) (sq_nonneg _))
    exact mul_le_mul hcoef hPQ (norm_nonneg _) hn
  have he : (truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N) =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P,Q]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖D*F*D-D'*F*D'‖+‖D'*(F-F')*D'‖ := norm_add_le _ _
    _ ≤ diagonalChange D D'*‖F‖+opNorm D'^2*‖F-F'‖ :=
      add_le_add (sandwich_difference_frobenius _ _ _) (sandwich_frobenius _ _)
    _ ≤ diagonalChange D D'*(fl1 f*opNorm D^2*‖M-N‖)+opNorm D'^2*
        ((fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hFF (sq_nonneg _))
    _ = _ := by unfold gMixed; ring

lemma projected_sub_bound {R : ℝ} (hR : 0 ≤ R) (M C : Matrix ι ι ℂ) :
    opNorm (matrixProject R hR M-C) ≤ R+opNorm C :=
  (opNorm_sub _ _).trans (add_le_add_left (matrixProject_bound R hR M).2 _)

lemma truncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedK f R hR B D C M) ≤ kBound f R D C := by
  apply (opNorm_add _ _).trans
  apply add_le_add opNorm_one_le
  exact (opNorm_mul _ _).trans
    (mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
      (opNorm_nonneg _) (g_constants_nonneg f hR B B D D).1)

lemma truncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M N : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedK f R hR B D C M-truncatedK f R hR B D C N‖ ≤
      kLip f R D C*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : truncatedK f R hR B D C M-truncatedK f R hR B D C N =
      (G M-G N)*(P M-C)+G N*(P M-P N) := by dsimp [truncatedK,G,P]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(G M-G N)*(P M-C)‖+‖G N*(P M-P N)‖ := norm_add_le _ _
    _ ≤ ‖G M-G N‖*opNorm (P M-C)+opNorm (G N)*‖P M-P N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ (gLip f D*‖M-N‖)*(R+opNorm C)+gBound f D*‖M-N‖ := by
      apply add_le_add
      · exact mul_le_mul (truncatedG_sub_norm _ _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
          (opNorm_nonneg _) (mul_nonneg (g_constants_nonneg f hR B B D D).2.1 (norm_nonneg _))
      · exact mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (matrixProject_sub_norm _ _ _ _)
          (norm_nonneg _) (g_constants_nonneg f hR B B D D).1
    _ = _ := by unfold kLip; ring

lemma truncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' C C' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N)‖ ≤
      kMixed f R B B' D D' C C'*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let G' := truncatedG f R hR B' D'
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : (truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N) =
      (G M*(P M-C)-G N*(P N-C))-(G' M*(P M-C')-G' N*(P N-C')) := by
    dsimp [truncatedK,G,G',P]; abel
  rw [he]
  have h₁ : (P M-C)-(P M-C') = -(C-C') := by abel
  have h₂ : (P M-C)-(P N-C) = P M-P N := by abel
  have h₃ : ((P M-C)-(P N-C))-((P M-C')-(P N-C')) = 0 := by abel
  have hh := product_four_point (G M) (G N) (G' M) (G' N) (P M-C) (P N-C) (P M-C') (P N-C')
  rw [h₃,h₁,h₂,opNorm_neg,norm_zero,mul_zero,add_zero] at hh
  apply hh.trans
  calc
    _ ≤ (gMixed f R B B' D D'*‖M-N‖)*(R+opNorm C)+
        (gLip f D'*‖M-N‖)*opNorm (C-C')+gChange f R B B' D D'*‖M-N‖ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (truncatedG_four_point f hR B B' D D' M N hB hB' hD hD')
            (projected_sub_bound hR M C) (opNorm_nonneg _)
            (mul_nonneg (g_constants_nonneg f hR B B' D D').2.2.2 (norm_nonneg _))
        · exact mul_le_mul_of_nonneg_right (truncatedG_sub_norm _ _ _ _ _ _ _ hB' hD') (opNorm_nonneg _)
      · exact mul_le_mul (truncatedG_parameter f hR B B' D D' N hB hB' hD hD')
          (matrixProject_sub_norm _ _ _ _) (norm_nonneg _)
          (g_constants_nonneg f hR B B' D D').2.2.1
    _ = _ := by unfold kMixed; ring

end SKGap.ComplexMatrix

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

lemma norm_liftMatrix (M : Matrix ι ι ℝ) : ‖liftMatrix M‖ = ‖M‖ :=
  Matrix.frobenius_norm_map_eq M Complex.ofReal (fun x => by simp)

omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_sub (M N : Matrix ι ι ℝ) :
    liftMatrix (M-N) = liftMatrix M-liftMatrix N := by ext i j; simp [liftMatrix]
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_conjTranspose (M : Matrix ι ι ℝ) :
    (liftMatrix M)ᴴ = liftMatrix Mᵀ := by ext i j; simp [liftMatrix]
omit [Fintype ι] [DecidableEq ι] in
lemma liftMatrix_hermitian (M : Matrix ι ι ℝ) (hM : Mᵀ = M) :
    (liftMatrix M)ᴴ = liftMatrix M := by rw [liftMatrix_conjTranspose,hM]

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealPart
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

lemma norm_realPart_le (M : Matrix ι ι ℂ) : ‖realPart M‖ ≤ ‖M‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  simp only [realPart,Matrix.map_apply,Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M i k)) 2

omit [Fintype ι] [DecidableEq ι] in
lemma realPart_sub (M N : Matrix ι ι ℂ) : realPart (M-N) = realPart M-realPart N := by
  ext i k; simp [realPart]

omit [DecidableEq ι] in
lemma reVec_norm_le (x : EuclideanSpace ℂ ι) : ‖reVec x‖ ≤ ‖x‖ := by
  have h := vec_norm_split x
  nlinarith [sq_nonneg ‖imVec x‖,norm_nonneg (reVec x),norm_nonneg x]

lemma realPart_operator (M : Matrix ι ι ℂ) (x : EuclideanSpace ℝ ι) :
    rlin (realPart M) x = reVec (clin M (liftVec x)) := by
  ext i
  change (∑ k, (M i k).re*x k) = (∑ k, M i k*(x k : ℂ)).re
  simp

lemma operator_realPart_le (M : Matrix ι ι ℂ) : opNorm (realPart M) ≤ ‖clin M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [realPart_operator]
  exact (reVec_norm_le _).trans ((clin M).le_opNorm (liftVec x) |>.trans_eq (by rw [norm_liftVec]))

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realTruncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M N : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    ‖realTruncatedK f R hR D C M-realTruncatedK f R hR D C N‖ ≤
      kLip f R (liftMatrix D) (liftMatrix C)*‖M-N‖ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  unfold realTruncatedK
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    truncatedK_sub_norm f hR _ _ _ (liftMatrix M) (liftMatrix N) hB hD'

lemma realTruncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    SKGap.opNorm (realTruncatedK f R hR D C M) ≤ kBound f R (liftMatrix D) (liftMatrix C) := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  exact (operator_realPart_le _).trans (truncatedK_opNorm f hR _ _ _ _ hB hD')

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

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma path_constants_bound (f : 𝓢(ℝ,ℂ)) {R j A z q : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (_hj : 0 ≤ j) (hA0 : 0 ≤ A) (hA : ∀ i, a i ≤ A)
    (hq : 0 ≤ q) (hqA : q ≤ j*A) (hz : z ∈ Icc (0:ℝ) 1) :
    ComplexMatrix.kBound f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathBound f R j A ∧
    ComplexMatrix.kLip f R (liftMatrix (pathDiagonal a z)) (liftMatrix (pathShift z q)) ≤ pathLip f R j A ∧
    opNorm (pathDiagonal a z*pathDiagonal a z) ≤ A := by
  have hd := pathDiagonal_opNorm hA0 hA hz
  have hc := (pathShift_opNorm (ι := ι) hz hq).trans hqA
  have hd2 : opNorm (pathDiagonal a z)^2 ≤ A := by
    have hh := pow_le_pow_left₀ (show 0 ≤ opNorm (pathDiagonal a z) from norm_nonneg _) hd 2
    rwa [sq_sqrt hA0] at hh
  have hd4 : opNorm (pathDiagonal a z)^4 ≤ A^2 := by
    calc
      _ = (opNorm (pathDiagonal a z)^2)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hd2 2
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  have hc0 : 0 ≤ R+opNorm (pathShift (ι := ι) z q) := add_nonneg hR (norm_nonneg _)
  unfold ComplexMatrix.kBound ComplexMatrix.kLip ComplexMatrix.gBound ComplexMatrix.gLip pathBound pathLip
  simp only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift]
  refine ⟨?_,?_,?_⟩
  · gcongr
  · gcongr
  · exact (opNorm_mul _ _).trans (by nlinarith)

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realProject_opNorm {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M) ≤ R :=
  (operator_realPart_le _).trans (ComplexMatrix.matrixProject_bound R hR (liftMatrix M)).2

lemma realProject_sub_norm {R : ℝ} (hR : 0 ≤ R) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M-realProject R hR N‖ ≤ ‖M-N‖ := by
  unfold realProject
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    ComplexMatrix.matrixProject_sub_norm R hR (liftMatrix M) (liftMatrix N)

lemma realProject_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (realProject (ι := ι) R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using realProject_sub_norm hR M N

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathCutoff
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathK_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (hA : 0 ≤ A) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (∀ M, opNorm (pathK f R hR j a z M) ≤ pathBound f R j A) ∧
    (∀ M N, ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ pathLip f R j A*‖M-N‖) := by
  have hq := diagonal_mean_bounds hj ha haA
  have hc := path_constants_bound f hR hj hA haA hq.1 hq.2 hz
  constructor
  · intro M
    exact (realTruncatedK_opNorm f hR _ _ M (diagonal_transpose _) (diagonal_transpose _)).trans hc.1
  · intro M N
    exact (realTruncatedK_sub_norm f hR _ _ M N (diagonal_transpose _) (diagonal_transpose _)).trans
      (mul_le_mul_of_nonneg_right hc.2.1 (norm_nonneg _))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealParameterIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Real Set
open scoped Matrix.Norms.Frobenius SchwartzMap
namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma truncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (B B' D D' C C' M : Matrix ι ι ℂ)
    (hB : Bᴴ=B) (hB' : B'ᴴ=B') (hD : Dᴴ=D) (hD' : D'ᴴ=D') :
    opNorm (truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M)≤
      kChange f R B B' D D' C C' := by
  have he : truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M=
    (truncatedG f R hR B D M-truncatedG f R hR B' D' M)*(matrixProject R hR M-C)+
      truncatedG f R hR B' D' M*(C'-C) := by unfold truncatedK;noncomm_ring
  rw [he]
  apply (opNorm_add _ _).trans
  apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
  have h1 := mul_le_mul (truncatedG_parameter f hR B B' D D' M hB hB' hD hD')
    (projected_sub_bound hR M C) (opNorm_nonneg _) (g_constants_nonneg f hR B B' D D').2.2.1
  have h2 := mul_le_mul_of_nonneg_right (truncatedG_opNorm f R hR B' D' M hB' hD')
    (opNorm_nonneg (C'-C))
  have hs : opNorm (C'-C)=opNorm (C-C') := by rw [← neg_sub C C',opNorm_neg]
  rw [hs] at h2
  simpa only [kChange,hs,gBound] using add_le_add h1 h2
end SKGap.ComplexMatrix
namespace SKGap.RealComplex
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma liftedSand_hermitian (D C : Matrix ι ι ℝ) (hD : Dᵀ=D) (hC : Cᵀ=C) :
    (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ=1+liftMatrix D*liftMatrix C*liftMatrix D := by
  simp [Matrix.conjTranspose_mul,liftMatrix_hermitian D hD,liftMatrix_hermitian C hC,mul_assoc]
lemma realTruncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    SKGap.opNorm (realTruncatedK f R hR D C M-realTruncatedK f R hR D' C' M)≤
      kChange f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') := by
  unfold realTruncatedK
  rw [← realPart_sub]
  exact (operator_realPart_le _).trans (truncatedK_parameter f hR _ _ _ _ _ _ _
    (liftedSand_hermitian D C hD hC) (liftedSand_hermitian D' C' hD' hC')
    (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD'))

lemma realTruncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M N : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    ‖(realTruncatedK f R hR D C M-realTruncatedK f R hR D C N)-
      (realTruncatedK f R hR D' C' M-realTruncatedK f R hR D' C' N)‖≤
      kMixed f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C')*‖M-N‖ := by
  unfold realTruncatedK
  rw [← realPart_sub,← realPart_sub,← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using! truncatedK_four_point f hR _ _ _ _ _ _
    (liftMatrix M) (liftMatrix N) (liftedSand_hermitian D C hD hC)
    (liftedSand_hermitian D' C' hD' hC') (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD')
end SKGap.RealComplex
end
end

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cutoff_parameter_constants (f : 𝓢(ℝ,ℂ))
    {R V T H δ : ℝ} (hR : 0≤R) (hV : 0≤V) (_hT : 0≤T) (hH : 0≤H) (hδ : 0≤δ)
    (B B' D D' C C' : Matrix ι ι ℂ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T)
    (hBD : opNorm (B-B')≤H*δ) (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    kChange f R B B' D D' C C'≤parameterKC f R V T H*δ ∧
    kMixed f R B B' D D' C C'≤parameterKM f R V T H*δ := by
  have hf0 := fourierMoment_nonneg f 0
  obtain ⟨hf1,hf2⟩ := fl_nonneg f
  have hDC : diagonalChange D D'≤(2*V)*δ := by
    unfold diagonalChange
    exact mul_le_mul (by linarith) hDD (opNorm_nonneg _) (by positivity)
  have hSC : shiftChange R B B' D D'≤(H+2*V*R)*δ := by
    unfold shiftChange
    have hh := add_le_add hBD (mul_le_mul_of_nonneg_right hDC hR)
    nlinarith only [hh]
  have hGH : 0≤H+2*V*R := by positivity
  have hgc : gChange f R B B' D D'≤parameterGC f R V H*δ := by
    unfold gChange parameterGC
    calc
      _ ≤ ((2*V)*δ)*fourierMoment f 0+V^2*fl1 f*((H+2*V*R)*δ) := by
        apply add_le_add (mul_le_mul_of_nonneg_right hDC hf0)
        apply mul_le_mul _ hSC (shiftChange_nonneg hR _ _ _ _) (by positivity)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf1
      _ = _ := by ring
  have hgm : gMixed f R B B' D D'≤parameterGM f R V H*δ := by
    unfold gMixed parameterGM
    calc
      _ ≤ ((2*V)*δ)*fl1 f*V^2+V^2*(fl1 f*((2*V)*δ)+fl2 f*(2*((H+2*V*R)*δ))*V^2) := by
        apply add_le_add
        · apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D) hD 2) (by positivity [fl_nonneg f]) (by positivity)
          exact mul_le_mul_of_nonneg_right hDC hf1
        · apply mul_le_mul (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) _ (by positivity [diagonalChange_nonneg D D',shiftChange_nonneg hR B B' D D']) (by positivity)
          apply add_le_add (mul_le_mul_of_nonneg_left hDC hf1)
          apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) (by positivity [opNorm_nonneg D']) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSC (by norm_num)) hf2
      _ = _ := by ring
  have hgc0 : 0≤parameterGC f R V H := by unfold parameterGC;positivity
  have hgm0 : 0≤parameterGM f R V H := by unfold parameterGM;positivity
  constructor
  · unfold kChange parameterKC
    calc
      _ ≤ (parameterGC f R V H*δ)*(R+T)+(V^2*fourierMoment f 0)*δ := by
        apply add_le_add
        · exact mul_le_mul hgc (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf0) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold kMixed parameterKM
    calc
      _ ≤ (parameterGM f R V H*δ)*(R+T)+(fl1 f*V^4)*δ+parameterGC f R V H*δ := by
        apply add_le_add _ hgc
        apply add_le_add
        · exact mul_le_mul hgm (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opNorm_nonneg D') hD' 4) hf1) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
end SKGap.ComplexMatrix
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

lemma sqrt_parameter_holder {a b δ : ℝ} (ha : 0≤a) (hb : 0≤b) (hδ : 0≤δ)
    (hab : |a-b|≤δ) : |sqrt a-sqrt b|≤ sqrt δ := by
  have ha2 := sq_sqrt ha
  have hb2 := sq_sqrt hb
  have hd2 := sq_sqrt hδ
  rcases le_total a b with hab'|hba
  · have hxy := sqrt_le_sqrt hab'
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg a)
    have hbd : b-a≤δ := by linarith [neg_le_abs (a-b)]
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]
  · have hxy := sqrt_le_sqrt hba
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hmul := mul_le_mul_of_nonneg_left hxy (sqrt_nonneg b)
    have had : a-b≤δ := (le_abs_self _).trans hab
    nlinarith [sqrt_nonneg a,sqrt_nonneg b,sqrt_nonneg δ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma pathDiagonal_parameter {a b : ι→ℝ} {δ : ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i)
    (hδ : 0≤δ) (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathDiagonal a 1-pathDiagonal b 1)≤ sqrt δ := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (sqrt_nonneg _) (fun i=>sqrt_parameter_holder (ha i) (hb i) hδ (hab i))

omit [DecidableEq ι] in
lemma mean_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (_hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    |(j/(Fintype.card ι:ℝ))*(∑ i,a i)-(j/(Fintype.card ι:ℝ))*(∑ i,b i)|≤j*δ := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (div_nonneg hj hn.le)]
  have hh : |∑ i,(a i-b i)|≤(Fintype.card ι:ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hab i)
  apply (mul_le_mul_of_nonneg_left hh (div_nonneg hj hn.le)).trans_eq
  field_simp

lemma pathShift_parameter [Nonempty ι] {a b : ι→ℝ} {j δ : ℝ} (hj : 0≤j) (hδ : 0≤δ)
    (hab : ∀ i,|a i-b i|≤δ) :
    opNorm (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)-
      pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))≤j*δ := by
  simp only [pathShift,one_mul,diagonal_sub]
  exact opNorm_diagonal_le (mul_nonneg hj hδ) (fun _=>mean_parameter hj hδ hab)
end SKGap
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma spectralShift_difference (D D' C C' : Matrix ι ι ℂ) : (1+D*C*D)-(1+D'*C'*D')=(D-D')*C*D+D'*(C-C')*D+D'*C'*(D-D') := by noncomm_ring

lemma complex_product_bound (M N : Matrix ι ι ℂ) {x y : ℝ} (hx : 0≤x)
    (hM : opNorm M≤x) (hN : opNorm N≤y) : opNorm (M*N)≤x*y :=
  (opNorm_mul M N).trans (mul_le_mul hM hN (opNorm_nonneg N) hx)

lemma complex_triple_bound (M N P : Matrix ι ι ℂ) {x y z : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hM : opNorm M≤x) (hN : opNorm N≤y) (hP : opNorm P≤z) :
    opNorm (M*N*P)≤x*y*z :=
  complex_product_bound (M*N) P (mul_nonneg hx hy) (complex_product_bound M N hx hM hN) hP

lemma complex_sum_three_bound (M N P : Matrix ι ι ℂ) :
    opNorm (M+N+P)≤opNorm M+opNorm N+opNorm P :=
  (opNorm_add (M+N) P).trans (add_le_add (opNorm_add M N) le_rfl)

lemma spectralShift_parameter (D D' C C' : Matrix ι ι ℂ) {V T δ : ℝ}
    (hV : 0≤V) (hT : 0≤T) (hδ : 0≤δ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T) (hC' : opNorm C'≤T)
    (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    opNorm ((1+D*C*D)-(1+D'*C'*D'))≤(2*V*T+V^2)*δ := by
  rw [spectralShift_difference]
  have h1 := complex_triple_bound (D-D') C D hδ hT hDD hC hD
  have h2 := complex_triple_bound D' (C-C') D hV hδ hD' hCD hD
  have h3 := complex_triple_bound D' C' (D-D') hV hT hD' hC' hDD
  calc
    _ ≤ opNorm ((D-D')*C*D)+opNorm (D'*(C-C')*D)+opNorm (D'*C'*(D-D')) := complex_sum_three_bound _ _ _
    _ ≤ δ*T*V+V*δ*V+V*T*δ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma parameter_sqrt_small {δ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) : δ≤ sqrt δ := by
  have hh := sq_sqrt hδ
  nlinarith [sqrt_nonneg δ,mul_nonneg hδ (sub_nonneg.mpr hδ1)]

lemma path_parameter_factors [Nonempty ι] {a b : ι→ℝ} {j A δ : ℝ}
    (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) :
    let D := liftMatrix (pathDiagonal a 1)
    let D' := liftMatrix (pathDiagonal b 1)
    let C := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i))
    let C' := liftMatrix (pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i))
    ComplexMatrix.opNorm D≤ sqrt A ∧ ComplexMatrix.opNorm D'≤ sqrt A ∧
    ComplexMatrix.opNorm C≤j*A ∧ ComplexMatrix.opNorm C'≤j*A ∧
    ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ ∧
    ComplexMatrix.opNorm ((1+D*C*D)-(1+D'*C'*D'))≤
      (2*sqrt A*(j*A)+(sqrt A)^2)*((1+j)*sqrt δ) := by
  intro D D' C C'
  have hz : (1:ℝ)∈Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hDa : ComplexMatrix.opNorm D≤ sqrt A := by
    simpa only [D,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA haA hz
  have hDb : ComplexMatrix.opNorm D'≤ sqrt A := by
    simpa only [D',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using pathDiagonal_opNorm hA hbA hz
  have hqa := diagonal_mean_bounds hj ha haA
  have hqb := diagonal_mean_bounds hj hb hbA
  have hCa : ComplexMatrix.opNorm C≤j*A := by
    simpa only [C,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqa.1).trans hqa.2
  have hCb : ComplexMatrix.opNorm C'≤j*A := by
    simpa only [C',ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using
      (pathShift_opNorm (ι:=ι) hz hqb.1).trans hqb.2
  have hDD : ComplexMatrix.opNorm (D-D')≤(1+j)*sqrt δ := by
    have hh : opNorm (pathDiagonal a 1-pathDiagonal b 1)≤(1+j)*sqrt δ :=
      (pathDiagonal_parameter ha hb hδ hab).trans (by nlinarith [sqrt_nonneg δ])
    simpa only [D,D',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh
  have hCC : ComplexMatrix.opNorm (C-C')≤(1+j)*sqrt δ := by
    have hh := pathShift_parameter hj hδ hab
    have hh' : j*δ≤(1+j)*sqrt δ := by
      have hmul := mul_le_mul_of_nonneg_left (parameter_sqrt_small hδ hδ1) hj
      nlinarith [sqrt_nonneg δ]
    simpa only [C,C',← liftMatrix_sub,ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hh.trans hh'
  exact ⟨hDa,hDb,hCa,hCb,hDD,hCC,ComplexMatrix.spectralShift_parameter _ _ _ _
    (sqrt_nonneg _) (mul_nonneg hj hA) (mul_nonneg (by linarith) (sqrt_nonneg _)) hDa hDb hCa hCb hDD hCC⟩

theorem pathK_parameter_holder [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (M N : Matrix ι ι ℝ) :
    let H := 2*sqrt A*(j*A)+(sqrt A)^2
    opNorm (pathK f R hR j a 1 M-pathK f R hR j b 1 M)≤
      ComplexMatrix.parameterKC f R (sqrt A) (j*A) H*((1+j)*sqrt δ) ∧
    ‖(pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
      (pathK f R hR j b 1 M-pathK f R hR j b 1 N)‖≤
      ComplexMatrix.parameterKM f R (sqrt A) (j*A) H*((1+j)*sqrt δ)*‖M-N‖ := by
  intro H
  obtain ⟨hDa,hDb,hCa,hCb,hDD,hCC,hBB⟩ := path_parameter_factors hj hA hδ hδ1 ha hb haA hbA hab
  let D := pathDiagonal a 1
  let D' := pathDiagonal b 1
  let C := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,a i)
  let C' := pathShift (ι:=ι) 1 ((j/(Fintype.card ι:ℝ))*∑ i,b i)
  have hH : 0≤H := by dsimp [H];positivity
  have hh := ComplexMatrix.cutoff_parameter_constants f hR (sqrt_nonneg A) (mul_nonneg hj hA) hH
    (show 0≤(1+j)*sqrt δ by positivity)
    (1+liftMatrix D*liftMatrix C*liftMatrix D) (1+liftMatrix D'*liftMatrix C'*liftMatrix D')
    (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') hDa hDb hCa hBB hDD hCC
  constructor
  · exact (realTruncatedK_parameter f hR D D' C C' M (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans hh.1
  · exact (realTruncatedK_four_point f hR D D' C C' M N (diagonal_transpose _)
      (diagonal_transpose _) (diagonal_transpose _) (diagonal_transpose _)).trans
        (mul_le_mul_of_nonneg_right hh.2 (norm_nonneg _))
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordRegularity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma matrixFactorProduct_opNorm (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (x : X) :
    opNorm (matrixFactorProduct F x) ≤ (R:ℝ)^F.length := by
  induction F with
  | nil => simpa using opNorm_one_le (ι:=ι)
  | cons f F ih =>
    rw [matrixFactorProduct_cons,List.length_cons,pow_succ']
    exact (opNorm_mul _ _).trans (mul_le_mul (hF f (List.mem_cons_self) x)
      (ih (fun p hp=>hF p (List.mem_cons_of_mem f hp))) (show 0 ≤ opNorm (matrixFactorProduct F x) from norm_nonneg _) R.coe_nonneg)

theorem matrixFactorProduct_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R)
    (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ((F.length:NNReal)*R^F.length) (matrixFactorProduct F) := by
  induction F with
  | nil => simp [matrixFactorProduct]
  | cons f F ih =>
    have hFt : ∀ p∈F,∀ x,opNorm (p x) ≤ R := fun p hp=>hF p (List.mem_cons_of_mem f hp)
    have hLt : ∀ p∈F,LipschitzWith R p := fun p hp=>hL p (List.mem_cons_of_mem f hp)
    have ht := ih hFt hLt
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,matrixFactorProduct_cons,matrixFactorProduct_cons]
    have he : f x*matrixFactorProduct F x-f y*matrixFactorProduct F y=
        f x*(matrixFactorProduct F x-matrixFactorProduct F y)+(f x-f y)*matrixFactorProduct F y := by noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (frobenius_mul_le_opNorm _ _) (frobenius_mul_le_opNorm_right _ _)).trans
    have hd : ‖matrixFactorProduct F x-matrixFactorProduct F y‖ ≤ ((F.length:ℝ)*(R:ℝ)^F.length)*dist x y := by
      simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using ht.dist_le_mul x y
    have hf : ‖f x-f y‖ ≤ (R:ℝ)*dist x y := by
      simpa only [dist_eq_norm] using (hL f List.mem_cons_self).dist_le_mul x y
    have hb := matrixFactorProduct_opNorm F hFt y
    have hp := hF f List.mem_cons_self x
    have h1 := mul_le_mul hp hd (norm_nonneg _) R.coe_nonneg
    have h2 := mul_le_mul hf hb (show 0 ≤ opNorm (matrixFactorProduct F y) from norm_nonneg _) (mul_nonneg R.coe_nonneg dist_nonneg)
    apply (add_le_add h1 h2).trans_eq
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,List.length_cons,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,pow_succ]
    ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordIncrement
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
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma word_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

omit [PseudoMetricSpace X] in
lemma real_product_four_point (a b c d e f g h : Matrix ι ι ℝ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e+‖c-d‖*opNorm (e-g)+
      opNorm (b-d)*‖e-f‖+opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h)=
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

theorem matrixWord_pair_increments (F : List ((X→Matrix ι ι ℝ)×(X→Matrix ι ι ℝ)))
    {B Δ : NNReal} (hF : ∀ p∈F,MatrixFactorPairBounds B Δ p.1 p.2) :
    (∀ x,opNorm (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x)≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun x=>matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by
  induction F with
  | nil =>
    constructor
    · intro x;simp [matrixFactorProduct,wordParameterCoeff,opNorm]
    · simp [matrixFactorProduct,wordMixedCoeff]
  | cons p F ih =>
    have hp := hF p List.mem_cons_self
    have hFt : ∀ q∈F,MatrixFactorPairBounds B Δ q.1 q.2 := fun q hq=>hF q (List.mem_cons_of_mem p hq)
    have ht := ih hFt
    have hbL : ∀ f∈F.map Prod.fst,∀ x,opNorm (f x)≤B := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftBound
    have hlL : ∀ f∈F.map Prod.fst,LipschitzWith B f := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftLip
    have htl := matrixFactorProduct_lipschitz (F.map Prod.fst) hbL hlL
    constructor
    · intro x
      simp only [List.map_cons,matrixFactorProduct_cons,List.length_cons,wordParameterCoeff,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow]
      have he : p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x=
        (p.1 x-p.2 x)*matrixFactorProduct (F.map Prod.fst) x+
        p.2 x*(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by noncomm_ring
      rw [he]
      apply (word_opNorm_add _ _).trans
      apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
      have h1 := mul_le_mul (hp.parameter x) (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) Δ.coe_nonneg
      have h2 := mul_le_mul (hp.rightBound x) (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _) B.coe_nonneg
      apply (add_le_add h1 h2).trans_eq
      simp only [List.length_map]
      ring
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm,List.map_cons,matrixFactorProduct_cons]
      have he : (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x)-
          (p.1 y*matrixFactorProduct (F.map Prod.fst) y-p.2 y*matrixFactorProduct (F.map Prod.snd) y)=
        (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.1 y*matrixFactorProduct (F.map Prod.fst) y)-
          (p.2 x*matrixFactorProduct (F.map Prod.snd) x-p.2 y*matrixFactorProduct (F.map Prod.snd) y) := by abel
      rw [he]
      apply (real_product_four_point _ _ _ _ _ _ _ _).trans
      have hi : ‖(p.1 x-p.1 y)-(p.2 x-p.2 y)‖≤(Δ:ℝ)*dist x y := by
        have hh := hp.increment.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1;abel
      have hr : ‖p.2 x-p.2 y‖≤(B:ℝ)*dist x y := by simpa only [dist_eq_norm] using hp.rightLip.dist_le_mul x y
      have hli : ‖matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y‖≤
          ((F.length:ℝ)*(B:ℝ)^F.length)*dist x y := by
        simpa only [dist_eq_norm,List.length_map,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using htl.dist_le_mul x y
      have hm : ‖(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y)-
          (matrixFactorProduct (F.map Prod.snd) x-matrixFactorProduct (F.map Prod.snd) y)‖≤
          ((wordMixedCoeff B F.length:ℝ)*Δ)*dist x y := by
        have hh := ht.2.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1;abel
      have h1 := mul_le_mul hi (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) (mul_nonneg Δ.coe_nonneg dist_nonneg)
      have h2 := mul_le_mul hr (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _)
        (mul_nonneg B.coe_nonneg dist_nonneg)
      have h3 := mul_le_mul (hp.parameter y) hli (norm_nonneg _) Δ.coe_nonneg
      have h4 := mul_le_mul (hp.rightBound y) hm (norm_nonneg _) B.coe_nonneg
      apply (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq
      simp only [List.length_map,List.length_cons,wordMixedCoeff,NNReal.coe_add,NNReal.coe_mul,
        NNReal.coe_natCast,NNReal.coe_pow]
      ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.eval_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (l : WordLetter ι) (hl : l.bounded D) :
    (∀ M,opNorm (l.eval f R hR j a z M) ≤ actualWordBound f R j A D) ∧
    LipschitzWith ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
      (l.eval f R hR j a z) := by
  have hconst := path_constants_nonneg f hR hj hA
  have hD' : D ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hR' : R ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have h1 : 1 ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hB : pathBound f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hL : pathLip f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  cases l with
  | diag d =>
    constructor
    · intro M;exact (opNorm_diagonal_le hD hl).trans hD'
    · exact (LipschitzWith.const (diagonal d)).weaken (show (0:NNReal) ≤ _ from zero_le)
  | noise =>
    constructor
    · intro M;exact (realProject_opNorm hR M).trans hR'
    · exact (realProject_lipschitz hR).weaken h1
  | inverse =>
    have hh := pathK_bounds f hR hj hA ha haA hz
    constructor
    · intro M;exact (hh.1 M).trans hB
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ actualWordBound f R j A D*‖M-N‖
      exact (hh.2 M N).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem actualWord_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∀ M,opNorm (actualWord f R hR j a z F M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (actualWord f R hR j a z F) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let G := F.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M) ≤ B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).2
  constructor
  · intro M
    simpa only [G,B,actualWord,List.length_map,NNReal.coe_mk] using! matrixFactorProduct_opNorm G hGb M
  · simpa only [G,B,actualWord,List.length_map] using! (@matrixFactorProduct_lipschitz ι (Matrix ι ι ℝ) _ _ (inferInstance : MetricSpace (Matrix ι ι ℝ)).toPseudoMetricSpace G B hGb hGl)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma wordHolderScale_constants (f : 𝓢(ℝ,ℂ)) (R A : ℝ) {j : ℝ} (hj : 0≤j) :
    ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A ∧
    ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A := by
  have hc := le_abs_self (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm := le_abs_self (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hc0 := abs_nonneg (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm0 := abs_nonneg (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have h1 : 0≤1+j := by linarith
  unfold wordHolderScale
  constructor
  · have h := mul_le_mul_of_nonneg_right hc h1
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hm h1
    nlinarith

lemma WordLetter.eval_pair [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  obtain ⟨hlb,hll⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
  obtain ⟨hmb,hml⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
  refine ⟨hlb,hmb,hll,hml,?_,?_⟩
  · intro M
    cases l <;> cases m <;> try contradiction
    · rename_i d e
      change opNorm (diagonal d-diagonal e)≤wordHolderScale f R j A*sqrt δ
      rw [Matrix.diagonal_sub]
      exact (opNorm_diagonal_le hδ hlm).trans ((parameter_sqrt_small hδ hδ1).trans
        (by nlinarith [wordHolderScale_ge_one f R A hj,sqrt_nonneg δ]))
    · simp [WordLetter.eval,opNorm]
    · exact ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M M).1).trans
        (by have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).1 (sqrt_nonneg δ)
            simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh)
  · cases l <;> cases m <;> try contradiction
    · rename_i d e
      exact (LipschitzWith.const (diagonal d-diagonal e)).weaken (show (0:NNReal)≤Δ from zero_le)
    · simpa only [WordLetter.eval,sub_self] using (LipschitzWith.const (0:Matrix ι ι ℝ)).weaken (show (0:NNReal)≤Δ from zero_le)
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖(pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
        (pathK f R hR j a 1 N-pathK f R hR j b 1 N)‖≤wordHolderScale f R j A*sqrt δ*‖M-N‖
      have he : (pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
          (pathK f R hR j a 1 N-pathK f R hR j b 1 N)=
          (pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
          (pathK f R hR j b 1 M-pathK f R hR j b 1 N) := by abel
      rw [he]
      apply ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M N).2).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).2 (sqrt_nonneg δ)
      simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [Fintype ι] [DecidableEq ι] in
lemma templateInverse_bounds {A : ℝ} (hA : 0 ≤ A) (θ : WordParameter m ι) (i : ι) :
    0 ≤ templateInverse A θ i ∧ templateInverse A θ i ≤ A := by
  obtain ⟨h0,h1⟩ := (θ (none,i)).property
  dsimp [templateInverse]
  constructor
  · positivity
  · nlinarith only [mul_le_mul_of_nonneg_left h1 hA]

omit [Fintype ι] [DecidableEq ι] in
lemma templateDiagonal_bound {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι) (k : Fin m) (i : ι) :
    |templateDiagonal D θ k i| ≤ D := by
  obtain ⟨h0,h1⟩ := (θ (some k,i)).property
  rw [templateDiagonal,abs_mul,abs_of_nonneg hD]
  have hf : |2*(θ (some k,i):ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hD

omit [Fintype ι] [DecidableEq ι] in
lemma templateWord_bounded {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι)
    (F : List (WordTemplateLetter m)) : ∀ l∈templateWord D θ F,l.bounded D := by
  intro l hl
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hl
  cases q with
  | diag k => exact templateDiagonal_bound hD θ k
  | noise => trivial
  | inverse => trivial

omit [DecidableEq ι] in
lemma template_coord_dist (θ η : WordParameter m ι) (s : Option (Fin m)×ι) :
    |(θ s:ℝ)-(η s:ℝ)| ≤ dist θ η := by
  simpa only [Subtype.dist_eq,Real.dist_eq] using dist_le_pi_dist θ η s

omit [DecidableEq ι] in
lemma templateInverse_dist {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (i : ι) :
    |templateInverse A θ i-templateInverse A η i| ≤ templateScale A D*dist θ η := by
  rw [templateInverse,templateInverse,←mul_sub,abs_mul,abs_of_nonneg hA]
  apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (none,i)) hA).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  dsimp [templateScale]
  linarith

omit [DecidableEq ι] in
lemma templateLetter_close {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (l : WordTemplateLetter m) :
    (l.realize D θ).close (templateScale A D*dist θ η) (l.realize D η) := by
  cases l with
  | noise => trivial
  | inverse => trivial
  | diag k =>
    intro i
    change |D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)| ≤ _
    have he : D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)=
        (2*D)*((θ (some k,i):ℝ)-(η (some k,i):ℝ)) := by ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D)]
    apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (some k,i)) (by positivity : 0 ≤ 2*D)).trans
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    dsimp [templateScale]
    linarith

omit [DecidableEq ι] in
lemma templateWord_paired {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (F : List (WordTemplateLetter m)) :
    ∀ p∈F.map (fun l=>(l.realize D θ,l.realize D η)),
      p.1.bounded D ∧ p.2.bounded D ∧ p.1.close (templateScale A D*dist θ η) p.2 := by
  intro p hp
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  exact ⟨templateWord_bounded hD θ F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),
    templateWord_bounded hD η F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),templateLetter_close hA hD θ η l⟩
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GlobalWordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.eval_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  have hG : wordHolderScale f R j A ≤ globalWordHolder f R j A D := by
    have hh := actualWordBound_pos f hR hj hA hD
    dsimp [globalWordHolder]
    linarith
  by_cases hs : δ ≤ 1
  · have hh := l.eval_pair f hR hj hA hD hδ hs ha hb haA hbA hab m hl hm hlm
    have hΔ : (⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩:NNReal) ≤ Δ :=
      mul_le_mul_of_nonneg_right hG (sqrt_nonneg _)
    exact ⟨hh.leftBound,hh.rightBound,hh.leftLip,hh.rightLip,
      fun M=>(hh.parameter M).trans hΔ,hh.increment.weaken hΔ⟩
  · have hδ1 : 1 ≤ sqrt δ := by simpa only [sqrt_one] using sqrt_le_sqrt (le_of_not_ge hs)
    have hGB : 2*(B:ℝ) ≤ globalWordHolder f R j A D := by
      have hh := wordHolderScale_ge_one f R A hj
      change 2*actualWordBound f R j A D ≤ wordHolderScale f R j A+2*actualWordBound f R j A D+1
      linarith
    have hBΔ : 2*(B:ℝ) ≤ (Δ:ℝ) := by
      change 2*(B:ℝ) ≤ globalWordHolder f R j A D*sqrt δ
      exact (le_mul_of_one_le_right (by positivity : 0 ≤ 2*(B:ℝ)) hδ1).trans
        (mul_le_mul_of_nonneg_right hGB (sqrt_nonneg _))
    obtain ⟨h1,h2⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
    obtain ⟨h3,h4⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
    refine ⟨h1,h3,h2,h4,?_,?_⟩
    · intro M
      exact (opNorm_sub _ _).trans ((add_le_add (h1 M) (h3 M)).trans (by
        change actualWordBound f R j A D + actualWordBound f R j A D ≤ (Δ:ℝ)
        change 2*actualWordBound f R j A D ≤ (Δ:ℝ) at hBΔ
        linarith))
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      rw [dist_eq_norm]
      have he : (l.eval f R hR j a 1 M-m.eval f R hR j b 1 M)-
          (l.eval f R hR j a 1 N-m.eval f R hR j b 1 N)=
          (l.eval f R hR j a 1 M-l.eval f R hR j a 1 N)-
          (m.eval f R hR j b 1 M-m.eval f R hR j b 1 N) := by abel
      rw [he]
      apply (norm_sub_le _ _).trans
      have h2' := h2.dist_le_mul M N
      have h4' := h4.dist_le_mul M N
      rw [dist_eq_norm] at h2' h4'
      calc
        _ ≤ (B:ℝ)*dist M N+(B:ℝ)*dist M N := add_le_add h2' h4'
        _ = (2*(B:ℝ))*dist M N := by ring
        _ ≤ (Δ:ℝ)*dist M N := mul_le_mul_of_nonneg_right hBΔ dist_nonneg

theorem actualWord_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (F : List (WordLetter ι×WordLetter ι))
    (hF : ∀ p∈F,p.1.bounded D ∧ p.2.bounded D ∧ p.1.close δ p.2) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) := by
  intro B Δ
  let G := F.map (fun p=>(p.1.eval f R hR j a 1,p.2.eval f R hR j b 1))
  have hG : ∀ p∈G,MatrixFactorPairBounds B Δ p.1 p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1,h2,h3⟩ := hF q hq
    exact WordLetter.eval_pair_global f hR hj hA hD hδ ha hb haA hbA hab q.1 q.2 h1 h2 h3
  simpa only [G,List.length_map,List.map_map,Function.comp_def,actualWord] using! matrixWord_pair_increments G hG
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GeneralTemplateRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem generalTemplateMatrix_increments [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨generalTemplateHolder f R j A D*sqrt (dist θ η),mul_nonneg (generalTemplateHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) := by
  intro B Δ
  have hK : 0 ≤ templateScale A D := by dsimp [templateScale];positivity
  have hh := actualWord_pair_global f hR hj hA hD (mul_nonneg hK dist_nonneg)
    (fun i=>(templateInverse_bounds hA θ i).1) (fun i=>(templateInverse_bounds hA η i).1)
    (fun i=>(templateInverse_bounds hA θ i).2) (fun i=>(templateInverse_bounds hA η i).2)
    (templateInverse_dist hA hD θ η)
    (F.map (fun l=>(l.realize D θ,l.realize D η))) (templateWord_paired hA hD θ η F)
  simpa only [generalTemplateMatrix,generalTemplateHolder,B,Δ,List.length_map,List.map_map,
    Function.comp_def,templateWord,Real.sqrt_mul hK,mul_assoc] using! hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_MatrixMeanContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable [TopologicalSpace T] [FirstCountableTopology T]

lemma matrixEntryMean_continuous (F : T→EuclideanSpace ℝ κ→Matrix ι ι ℝ)
    (hF : ∀ θ,∃ L,LipschitzWith L (F θ)) (hc : ∀ x,Continuous (fun θ=>F θ x))
    {C : ℝ} (hb : ∀ θ x i k,|F θ x i k| ≤ C) :
    Continuous (fun θ=>matrixEntryMean (F θ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply continuous_of_dominated (bound:=fun _=>C)
  · intro θ
    obtain ⟨L,hL⟩ := hF θ
    exact (gaussianProduct_integrable_lipschitz (matrixEntry_lip hL i k)).aestronglyMeasurable
  · intro θ
    exact ae_of_all _ (fun g=>by simpa only [norm_eq_abs] using hb θ (WithLp.toLp 2 g) i k)
  · exact integrable_const _
  · exact ae_of_all _ (fun g=>(hc (WithLp.toLp 2 g)).matrix_elem i k)

lemma matrixCentered_continuous (F : T→EuclideanSpace ℝ κ→Matrix ι ι ℝ)
    (hF : ∀ θ,∃ L,LipschitzWith L (F θ)) (hc : ∀ x,Continuous (fun θ=>F θ x))
    {C : ℝ} (hb : ∀ θ x i k,|F θ x i k| ≤ C) (x : EuclideanSpace ℝ κ) :
    Continuous (fun θ=>matrixCentered (F θ) x) := by
  exact (hc x).sub (matrixEntryMean_continuous F hF hc hb)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma real_continuous_of_sqrt_increment {X : Type*} [PseudoMetricSpace X] {g : X→ℝ} {C : ℝ}
    (h : ∀ x y,|g x-g y| ≤ C*sqrt (dist x y)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun x=>norm_nonneg _))
    (Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using h x y))
  have hc : Continuous (fun x : X=>C*sqrt (dist x y)) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.dist continuous_const))
  simpa only [dist_self,Real.sqrt_zero,mul_zero] using hc.tendsto y

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma generalTemplateMatrix_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (M : Matrix ι ι ℝ) :
    Continuous (fun θ : WordParameter m ι=>generalTemplateMatrix f R hR j A D F θ M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply real_continuous_of_sqrt_increment (C:=
    (wordParameterCoeff ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩ F.length:ℝ)*generalTemplateHolder f R j A D)
  intro θ η
  have hh := (generalTemplateMatrix_increments f hR hj hA hD F θ η).1 M
  apply (matrix_entry_le_opNorm _ i k).trans
  simpa only [NNReal.coe_mk,mul_assoc] using! hh

lemma generalTemplateMatrix_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) :
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (generalTemplateMatrix f R hR j A D F θ) := by
  have hh := actualWord_bounds f hR hj hA hD
    (fun i=>(templateInverse_bounds hA θ i).1) (fun i=>(templateInverse_bounds hA θ i).2)
    ⟨zero_le_one,le_rfl⟩ (templateWord D θ F) (templateWord_bounded hD θ F)
  simpa only [generalTemplateMatrix,templateWord,List.length_map] using hh

lemma generalTemplateGaussian_centered_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (r : ℝ)
    (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    Continuous (fun θ : WordParameter m ι=>matrixCentered
      (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>generalTemplateMatrix f R hR j A D F θ (goeMatrix r x)) g) := by
  apply matrixCentered_continuous
  · intro θ
    exact ⟨_,(generalTemplateMatrix_bounds f hR hj hA hD F θ).2.comp (goeMatrix_L2_lipschitz r)⟩
  · intro x
    exact generalTemplateMatrix_continuous f hR hj hA hD F _
  · intro θ x i k
    exact (matrix_entry_le_opNorm _ i k).trans ((generalTemplateMatrix_bounds f hR hj hA hD F θ).1 _)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_MatrixNormTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma matrixWordSeminorm_lipschitz (p : Bool) : LipschitzWith 1 (matrixWordSeminorm (ι:=ι) p) := by
  cases p
  · exact diagonalSeminorm_lipschitz
  · exact offDiagonalSeminorm_lipschitz
lemma matrixWordSeminorm_add (p : Bool) (M N : Matrix ι ι ℝ) :
    matrixWordSeminorm p (M+N)≤ matrixWordSeminorm p M+matrixWordSeminorm p N := by
  cases p
  · exact diagonalSeminorm_add M N
  · exact offDiagonalSeminorm_add M N

lemma matrixCentered_sub {F G : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L K : NNReal} (hF : LipschitzWith L F) (hG : LipschitzWith K G) (x : EuclideanSpace ℝ κ) :
    matrixCentered (fun y=>F y-G y) x=matrixCentered F x-matrixCentered G x := by
  have hm : matrixEntryMean (fun y=>F y-G y)=matrixEntryMean F-matrixEntryMean G := by
    ext i k
    exact integral_sub (gaussianProduct_integrable_lipschitz (matrixEntry_lip hF i k))
      (gaussianProduct_integrable_lipschitz (matrixEntry_lip hG i k))
  simp only [matrixCentered,hm]
  abel

lemma gaussianProduct_centered_matrix_tail {F : EuclideanSpace ℝ κ→Matrix ι ι ℝ}
    {L : NNReal} (hF : LipschitzWith L F) (hL : 0<L) (p : Bool) {u : ℝ} (hu : 0≤u) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<
        matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))}≤
      ENNReal.ofReal (exp (-2*u^2/(π^2*(L:ℝ)^2))) := by
  let μ := Measure.pi (fun _ : κ=>gaussianReal 0 1)
  let X : (κ→ℝ)→ℝ := fun g=>matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))
  have hXL : LipschitzWith L (fun x : EuclideanSpace ℝ κ=>X x.ofLp) := by
    simpa only [X,WithLp.toLp_ofLp,one_mul,Function.comp_def] using
      (matrixWordSeminorm_lipschitz p).comp (matrixCentered_lipschitz hF)
  have hE : (∫ g,X g ∂μ)≤ matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ) := by
    cases p
    · exact (gaussianProduct_centered_matrix_norms hF hL).1
    · exact (gaussianProduct_centered_matrix_norms hF hL).2
  have htail := gaussianProduct_upper_tail_lipschitz hXL hL hu
  have hmono : μ {g | matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g}≤
      μ {g | u≤X g-∫ h,X h ∂μ} := by
    apply measure_mono
    intro g hg
    change matrixNormConstant*sqrt (Fintype.card ι)*(L:ℝ)+u<X g at hg
    change u≤X g-∫ h,X h ∂μ
    linarith only [hg,hE]
  apply hmono.trans
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal htail
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {κ : Type*} [Fintype κ]

lemma gaussianMatrix_scaled_semnorm_tail {n : ℕ} (hn : 1 ≤ n)
    {F : EuclideanSpace ℝ κ→Matrix (Fin n) (Fin n) ℝ} {H r T s : ℝ}
    (hH : 0<H) (hr : 0 < r) (hT : 0 ≤ T) (hs : 0 ≤ s)
    (hF : LipschitzWith (Real.toNNReal (H*r/sqrt n)) F) (p : Bool) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | (matrixNormConstant*H+T*s)*r< matrixWordSeminorm p (matrixCentered F (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-2*T^2*s^2*(n:ℝ)/(π^2*H^2))) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnS := sqrt_pos.mpr hn0
  have hL : 0<Real.toNNReal (H*r/sqrt n) := by exact_mod_cast (Real.toNNReal_pos.mpr (div_pos (mul_pos hH hr) hnS))
  have hh := gaussianProduct_centered_matrix_tail hF hL p (mul_nonneg (mul_nonneg hT hs) hr.le)
  have he : (matrixNormConstant*sqrt (Fintype.card (Fin n))*(Real.toNNReal (H*r/sqrt n):ℝ)+T*s*r)=
      (matrixNormConstant*H+T*s)*r := by
    rw [Fintype.card_fin,Real.coe_toNNReal _ (by positivity)]
    field_simp
  have he' : -2*(T*s*r)^2/(π^2*(Real.toNNReal (H*r/sqrt n):ℝ)^2)=
      -2*T^2*s^2*(n:ℝ)/(π^2*H^2) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    field_simp
    rw [sq_sqrt hn0.le]
  rw [he,he'] at hh
  exact hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ChainingCore
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology

lemma subadditive_chain_finite {E : Type*} [AddCommGroup E] (p : E→ℝ)
    (hp : ∀ x y,p (x+y) ≤ p x+p y) (u : ℕ→E) (r : ℕ→ℝ)
    (hr : ∀ k,p (u (k+1)-u k) ≤ r k) (n : ℕ) :
    p (u n) ≤ p (u 0)+∑ k∈Finset.range n,r k := by
  induction n with
  | zero => simp
  | succ n hn =>
      have hh := hp (u n) (u (n+1)-u n)
      rw [add_sub_cancel] at hh
      rw [Finset.sum_range_succ]
      linarith only [hh,hn,hr n]

lemma subadditive_chain_limit {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y) ≤ p x+p y)
    (u : ℕ→E) {x : E} (hu : Tendsto u atTop (𝓝 x)) (r : ℕ→ℝ)
    (hr0 : ∀ k,0 ≤ r k) (hrs : Summable r) (hr : ∀ k,p (u (k+1)-u k) ≤ r k) :
    p x ≤ p (u 0)+∑' k,r k := by
  apply le_of_tendsto (hc.tendsto x |>.comp hu)
  exact Eventually.of_forall (fun n=>(subadditive_chain_finite p hp u r hr n).trans
    (add_le_add_right (hrs.sum_le_tsum (Finset.range n) (fun i _=>hr0 i)) _))

lemma arithmetic_half_geometric_hasSum :
    HasSum (fun k : ℕ=>((k:ℝ)+1)*(1/2:ℝ)^k) 4 := by
  have h₁ := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h₂ := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have h : HasSum (fun k : ℕ => ((k:ℝ)+1)*(1/2:ℝ)^k)
      (1/2/(1-1/2)^2+(1-1/2)⁻¹) := by
    convert h₁.add h₂ using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    ring
  norm_num at h
  exact h

theorem continuous_chaining_probability
    {Ω T E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [TopologicalSpace T] [AddCommGroup E] [TopologicalSpace E]
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y) ≤ p x+p y)
    (F : T→Ω→E) (hF : ∀ ω,Continuous (fun t=>F t ω))
    (S : Set T) (ι : ℕ→Type*) [∀ k,Fintype (ι k)]
    (v : ∀ k,ι k→T) (edges : ∀ k,Finset (ι k×ι (k+1)))
    (hcover : ∀ t∈S,∃ a : ∀ k,ι k,
      (∀ k,(a k,a (k+1))∈edges k) ∧ Tendsto (fun k=>v k (a k)) atTop (𝓝 t))
    (r : ℕ→ℝ) (hr0 : ∀ k,0 ≤ r k) (hrs : Summable r)
    (b : ℝ) (q₀ : ℝ≥0∞) (q : ℕ→ℝ≥0∞)
    (hb : ∀ i,μ {ω | b < p (F (v 0 i) ω)} ≤ q₀)
    (hi : ∀ k, ∀ e∈edges k,μ {ω | r k < p (F (v (k+1) e.2) ω-F (v k e.1) ω)} ≤ q k) :
    μ {ω | ∃ t∈S,b+(∑' k,r k) < p (F t ω)} ≤
      (Fintype.card (ι 0):ℝ≥0∞)*q₀+∑' k,((edges k).card:ℝ≥0∞)*q k := by
  classical
  let B : Set Ω := ⋃ i : ι 0,{ω | b < p (F (v 0 i) ω)}
  let I : ℕ→Set Ω := fun k=>⋃ e∈edges k,{ω | r k < p (F (v (k+1) e.2) ω-F (v k e.1) ω)}
  have hs : {ω | ∃ t∈S,b+(∑' k,r k) < p (F t ω)} ⊆ B ∪ ⋃ k,I k := by
    intro ω hω
    by_contra hh
    have hh' := not_or.mp hh
    obtain ⟨t,ht,htp⟩ := hω
    obtain ⟨a,ha,hat⟩ := hcover t ht
    have hbase : p (F (v 0 (a 0)) ω) ≤ b := by
      by_contra hn
      exact hh'.1 (mem_iUnion.mpr ⟨a 0,not_le.mp hn⟩)
    have hinc : ∀ k,p (F (v (k+1) (a (k+1))) ω-F (v k (a k)) ω) ≤ r k := by
      intro k
      by_contra hn
      apply hh'.2
      exact mem_iUnion.mpr ⟨k,mem_iUnion₂.mpr ⟨(a k,a (k+1)),ha k,not_le.mp hn⟩⟩
    have hl := subadditive_chain_limit p hc hp (fun k=>F (v k (a k)) ω)
      ((hF ω).tendsto t |>.comp hat) r hr0 hrs hinc
    linarith only [hl,hbase,htp]
  apply (measure_mono hs).trans
  apply (measure_union_le _ _).trans
  apply add_le_add
  · exact (measure_iUnion_fintype_le μ _).trans ((Finset.sum_le_sum (fun i _=>hb i)).trans_eq (by simp))
  · apply (measure_iUnion_le I).trans
    apply ENNReal.tsum_le_tsum
    intro k
    apply (measure_biUnion_finset_le (edges k) _).trans
    exact (Finset.sum_le_sum (fun e he=>hi k e he)).trans_eq (by simp)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology

lemma exponential_series_bound {c : ℝ} (hc : log 2 ≤ c) :
    (∑' k : ℕ,ENNReal.ofReal (exp (-c*((k:ℝ)+1)))) ≤ ENNReal.ofReal (2*exp (-c)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (log_pos (by norm_num : (1:ℝ)<2)) hc
  have hr : exp (-c) < 1 := by rw [exp_lt_one_iff];linarith
  have hr2 : exp (-c) ≤ 1/2 := by
    rw [← exp_log (by norm_num : (0:ℝ)<(1/2))]
    apply exp_le_exp.mpr
    rw [log_div (by norm_num) (by norm_num),log_one]
    linarith only [hc]
  have he (k : ℕ) : exp (-c*((k:ℝ)+1))=exp (-c)*exp (-c)^k := by
    rw [← exp_nat_mul,← exp_add]
    congr 1;ring
  have hs : HasSum (fun k : ℕ=>exp (-c*((k:ℝ)+1))) (exp (-c)*(1-exp (-c))⁻¹) := by
    simpa only [he] using (hasSum_geometric_of_lt_one (exp_pos (-c)).le hr).mul_left (exp (-c))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _=>(exp_pos _).le) hs.summable,hs.tsum_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith only [hr] : 0 < 1-exp (-c))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hr2 (exp_pos (-c)).le]

lemma chaining_entropy_tail_product {n : ℕ} (_hn : 1 ≤ n)
    {A B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hA : B+c ≤ A)
    (k : ℕ) {m q : ℝ≥0∞}
    (hm : m ≤ ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))))
    (hq : q ≤ ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    m*q ≤ ENNReal.ofReal (exp (-c*(n:ℝ)*((k:ℝ)+1))) := by
  apply (mul_le_mul' hm hq).trans
  rw [← ENNReal.ofReal_mul (exp_pos _).le,← exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply exp_le_exp.mpr
  have hkn : 1 ≤ (k:ℝ)+1 := by
    have hk : (0:ℝ) ≤ k := by positivity
    linarith only [hk]
  have hnn : 0 ≤ (n:ℝ) := by positivity
  have hA0 : 0 ≤ A := by linarith
  have hs : (k:ℝ)+1 ≤ ((k:ℝ)+1)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hA0
  have hh' := mul_le_mul_of_nonneg_right hA (show 0 ≤ (k:ℝ)+1 by positivity)
  have hh'' := mul_le_mul_of_nonneg_right (show c*((k:ℝ)+1) ≤ A*((k:ℝ)+1)^2-B*((k:ℝ)+1) by linarith only [hh,hh']) hnn
  linarith only [hh'']

lemma chaining_entropy_series {n : ℕ} (hn : 1 ≤ n)
    {A B c : ℝ} (hB : 0 ≤ B) (hc : log 2 ≤ c) (hA : B+c ≤ A)
    (m q : ℕ→ℝ≥0∞)
    (hm : ∀ k,m k ≤ ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))))
    (hq : ∀ k,q k ≤ ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    (∑' k,m k*q k) ≤ ENNReal.ofReal (2*exp (-c*(n:ℝ))) := by
  have hc0 : 0 < c := lt_of_lt_of_le (log_pos (by norm_num : (1:ℝ)<2)) hc
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply (ENNReal.tsum_le_tsum (fun k=>chaining_entropy_tail_product hn hB hc0 hA k (hm k) (hq k))).trans
  have hcn : log 2 ≤ c*(n:ℝ) := hc.trans (by nlinarith only [hn',hc0])
  simpa only [neg_mul] using exponential_series_bound hcn
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BoxChaining
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma boxMesh_base_exp : (Fintype.card (α→Fin (4^0+1)):ℝ)≤exp (log 16*(Fintype.card α:ℝ)) := by
  have hh : (Fintype.card (α→Fin (4^0+1)):ℝ)≤(16:ℝ)^(Fintype.card α) := by
    simp only [Fintype.card_fun,Fintype.card_fin,pow_zero];norm_num
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  apply hh.trans_eq
  rw [←exp_log (by norm_num : (0:ℝ)<16),←exp_nat_mul]
  simp only [log_exp]
  congr 1;ring

theorem box_chaining_probability {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [TopologicalSpace E] (μ : Measure Ω)
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y)≤p x+p y)
    (F : (α→Icc (0:ℝ) 1)→Ω→E) (hF : ∀ ω,Continuous (fun t=>F t ω))
    {n : ℕ} (hn : 1≤n) {A B : ℝ} (hB : 0≤B) (hA : B+1≤A)
    (hdim : log 16*(Fintype.card α:ℝ)≤B*(n:ℝ))
    (b : ℝ) (r : ℕ→ℝ) (hr : ∀ k,0 ≤ r k) (hrs : Summable r)
    (hb : ∀ θ,μ {ω | b<p (F θ ω)}≤ENNReal.ofReal (exp (-A*(n:ℝ))))
    (hi : ∀ k θ η,dist θ η≤2*(1/4:ℝ)^k→
      μ {ω | r k<p (F θ ω-F η ω)}≤ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    μ {ω | ∃ θ,b+(∑' k,r k)<p (F θ ω)}≤ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  classical
  have hq := continuous_chaining_probability μ p hc hp F hF univ
    (fun k=>α→Fin (4^k+1)) boxMeshPoint boxMeshEdges (by
      intro θ _
      refine ⟨boxMeshIndex θ,?_,boxMeshIndex_tendsto θ⟩
      intro k
      simpa only [boxMeshEdges,Finset.mem_filter,Finset.mem_univ,true_and] using boxMeshIndex_increment θ k)
    r hr hrs b (ENNReal.ofReal (exp (-A*(n:ℝ))))
    (fun k=>ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ))))
    (fun i=>hb (boxMeshPoint 0 i)) (by
      intro k e he
      exact hi k _ _ (Finset.mem_filter.mp he).2)
  simp only [mem_univ,true_and] at hq
  apply hq.trans
  have hc1 : log 2≤(1:ℝ) := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢;exact hh
  have hbcard : (Fintype.card (α→Fin (4^0+1)):ℝ≥0∞)≤ENNReal.ofReal (exp (B*(n:ℝ))) := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (boxMesh_base_exp.trans (exp_le_exp.mpr hdim))
  have hbcost := chaining_entropy_tail_product hn hB (by norm_num : (0:ℝ)<1) hA 0
    (m := (Fintype.card (α→Fin (4^0+1)):ℝ≥0∞))
    (q := ENNReal.ofReal (exp (-A*(n:ℝ))))
    (by simpa only [Nat.cast_zero,zero_add,mul_one] using hbcard) (by simp)
  have hecard (k : ℕ) : ((boxMeshEdges (α:=α) k).card:ℝ≥0∞)≤ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))) := by
    rw [←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    apply (boxMesh_edges_exp k _).trans
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hdim (by positivity : 0≤(k:ℝ)+1)
    nlinarith only [hh]
  have hicost := chaining_entropy_series hn hB hc1 hA
    (fun k=>((boxMeshEdges (α:=α) k).card:ℝ≥0∞))
    (fun k=>ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) hecard (fun _=>le_rfl)
  apply (add_le_add hbcost hicost).trans_eq
  simp only [Nat.cast_zero,zero_add,mul_one,one_mul,neg_mul]
  rw [←ENNReal.ofReal_add (exp_pos _).le (by positivity)]
  congr 1;ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianMatrixChaining
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {κ α : Type*} [Fintype κ] [Fintype α] [DecidableEq α]

lemma gaussianMatrixChain_exponent {H B s : ℝ} (hH : 0<H) (hB : 0 ≤ B) (n : ℕ) :
    -2*(π*H*sqrt (B+1))^2*s^2*(n:ℝ)/(π^2*H^2)=
      -(2*(B+1))*s^2*(n:ℝ) := by
  rw [mul_pow,mul_pow,sq_sqrt (by linarith : 0 ≤ B+1)]
  field_simp

theorem gaussianMatrix_box_chaining {n : ℕ} (hn : 1 ≤ n) {H B : ℝ}
    (hH : 0<H) (hB : 0 ≤ B) (hdim : log 16*(Fintype.card α:ℝ) ≤ B*(n:ℝ))
    (F : (α→Icc (0:ℝ) 1)→EuclideanSpace ℝ κ→Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ θ,LipschitzWith (Real.toNNReal (H/sqrt n)) (F θ))
    (hi : ∀ k θ η,dist θ η ≤ 2*(1/4:ℝ)^k→
      LipschitzWith (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n)) (fun x=>F θ x-F η x))
    (hc : ∀ g : κ→ℝ,Continuous (fun θ=>matrixCentered (F θ) (WithLp.toLp 2 g)))
    (p : Bool) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | ∃ θ,gaussianMatrixChainConstant H B< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  let T := π*H*sqrt (B+1)
  let b := matrixNormConstant*H+T
  have hT : 0 ≤ T := by dsimp [T];positivity
  have hC : 0 ≤ matrixNormConstant := zero_le_one.trans matrixNormConstant_bounds.1
  have hb0 : 0 ≤ b := add_nonneg (mul_nonneg hC hH.le) hT
  let r : ℕ→ℝ := fun k=>b*((k:ℝ)+1)*(1/2:ℝ)^k
  have hsum : HasSum r (b*4) := by
    have he : r=(fun k : ℕ=>b*(((k:ℝ)+1)*(1/2:ℝ)^k)) := by
      funext k
      dsimp [r]
      ring
    rw [he]
    exact arithmetic_half_geometric_hasSum.mul_left b
  have hbase (θ : α→Icc (0:ℝ) 1) : (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | b< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-(2*(B+1))*(n:ℝ))) := by
    have hh := gaussianMatrix_scaled_semnorm_tail hn hH (by norm_num : (0:ℝ)<1) hT
      (by norm_num : (0:ℝ) ≤ 1) (F:=F θ) (by simpa only [mul_one] using hF θ) p
    rw [gaussianMatrixChain_exponent hH hB] at hh
    simpa only [T,b,mul_one,one_pow] using hh
  have hincr (k : ℕ) (θ η : α→Icc (0:ℝ) 1) (hθ : dist θ η ≤ 2*(1/4:ℝ)^k) :
      (Measure.pi (fun _ : κ=>gaussianReal 0 1))
      {g | r k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (exp (-(2*(B+1))*((k:ℝ)+1)^2*(n:ℝ))) := by
    have hh := gaussianMatrix_scaled_semnorm_tail hn hH (by positivity : (0:ℝ)<(1/2:ℝ)^k) hT
      (by positivity : 0 ≤ (k:ℝ)+1) (hi k θ η hθ) p
    rw [gaussianMatrixChain_exponent hH hB] at hh
    simp_rw [matrixCentered_sub (hF θ) (hF η)] at hh
    apply (measure_mono (show {g | r k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))}⊆
      {g | (matrixNormConstant*H+T*((k:ℝ)+1))*(1/2:ℝ)^k< matrixWordSeminorm p (matrixCentered (F θ) (WithLp.toLp 2 g)-matrixCentered (F η) (WithLp.toLp 2 g))} from ?_)).trans hh
    intro g hg
    change r k<_ at hg
    change (matrixNormConstant*H+T*((k:ℝ)+1))*(1/2:ℝ)^k<_
    apply lt_of_le_of_lt _ hg
    dsimp [r,b]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [mul_nonneg (mul_nonneg hC hH.le) (Nat.cast_nonneg k)]
  have hh := box_chaining_probability (Measure.pi (fun _ : κ=>gaussianReal 0 1))
    (matrixWordSeminorm p) (matrixWordSeminorm_lipschitz p).continuous (matrixWordSeminorm_add p)
    (fun θ g=>matrixCentered (F θ) (WithLp.toLp 2 g)) hc hn hB (by linarith : B+1 ≤ 2*(B+1))
    hdim b r (fun k=>by dsimp [r];positivity) hsum.summable hbase hincr
  rw [hsum.tsum_eq] at hh
  have he : b+b*4=gaussianMatrixChainConstant H B := by dsimp [b,T,gaussianMatrixChainConstant];ring
  rwa [he] at hh
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TemplateChaining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

lemma sqrt_mesh_increment {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) (h : δ ≤ 2*(1/4:ℝ)^k) :
    sqrt δ ≤ 2*(1/2:ℝ)^k := by
  have he : (1/4:ℝ)^k=(1/2:ℝ)^k*(1/2:ℝ)^k := by rw [←mul_pow]; norm_num
  rw [he] at h
  have hs := sq_sqrt hδ
  have hp : 0 ≤ (1/2:ℝ)^k := by positivity
  nlinarith [sqrt_nonneg δ]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem generalTemplateWord_gaussian_chaining {m : ℕ} (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ θ : WordParameter m (Fin n),C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let L : NNReal := (F.length:NNReal)*B^F.length
  let V : NNReal := wordMixedCoeff B F.length*⟨generalTemplateHolder f R j A D,generalTemplateHolder_nonneg f hR hj hA hD⟩
  let H : ℝ := 1+((L:ℝ)+2*V)*sqrt (2*j)
  let E : ℝ := log 16*((m:ℝ)+1)
  have hH : 0<H := by dsimp [H];positivity
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hHL : (L:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg V,sqrt_nonneg (2*j)]
  have hHV : 2*(V:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg L,sqrt_nonneg (2*j)]
  refine ⟨gaussianMatrixChainConstant H E,?_,?_⟩
  · have hc := matrixNormConstant_bounds.1
    dsimp [gaussianMatrixChainConstant]
    have hh : 0 < matrixNormConstant*H := mul_pos (by linarith) hH
    positivity
  · intro n hn p
    let : NeZero n := ⟨by omega⟩
    have hdim : log 16*(Fintype.card (Option (Fin m)×Fin n):ℝ) ≤ E*(n:ℝ) := by
      simp only [Fintype.card_prod,Fintype.card_option,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      dsimp [E]
      ring_nf
      exact le_rfl
    let T : WordParameter m (Fin n)→EuclideanSpace ℝ (MatrixCoordinates (Fin n))→Matrix (Fin n) (Fin n) ℝ :=
      fun θ x=>generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)
    have hsqrt : sqrt (2*(j/n))=sqrt (2*j)/sqrt n := by
      rw [show 2*(j/n)=(2*j)/n by ring,Real.sqrt_div (by positivity)]
    have hT (θ : WordParameter m (Fin n)) : LipschitzWith (Real.toNNReal (H/sqrt n)) (T θ) := by
      have hh := (generalTemplateMatrix_bounds f hR hj hA hD F θ).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (L:ℝ)*sqrt (2*(j/n)) ≤ (Real.toNNReal (H/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      calc
        _ = ((L:ℝ)*sqrt (2*j))/sqrt n := by ring
        _ ≤ H/sqrt n := div_le_div_of_nonneg_right hHL (sqrt_nonneg _)
    have hi (k : ℕ) (θ η : WordParameter m (Fin n)) (hθη : dist θ η ≤ 2*(1/4:ℝ)^k) :
        LipschitzWith (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n)) (fun x=>T θ x-T η x) := by
      have hh := (generalTemplateMatrix_increments f hR hj hA hD F θ η).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (((wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η)))*sqrt (2*(j/n))) ≤
        (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      have he : (wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η))=
          (V:ℝ)*sqrt (dist θ η) := by
        change (wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η)) =
          ((wordMixedCoeff B F.length:ℝ)*generalTemplateHolder f R j A D)*sqrt (dist θ η)
        ring
      rw [he]
      calc
        _ ≤ (V:ℝ)*(2*(1/2:ℝ)^k)*(sqrt (2*j)/sqrt n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_mesh_increment dist_nonneg k hθη) V.coe_nonneg) (by positivity)
        _ = (2*(V:ℝ)*sqrt (2*j))*(1/2:ℝ)^k/sqrt n := by ring
        _ ≤ H*(1/2:ℝ)^k/sqrt n := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hHV (by positivity)) (sqrt_nonneg _)
    exact gaussianMatrix_box_chaining hn hH hE hdim T hT hi
      (fun g=>generalTemplateGaussian_centered_continuous f hR hj hA hD F (j/n) (WithLp.toLp 2 g)) p
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TemplatePatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem all_generalTemplateWords_gaussian_chaining {m : ℕ} (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ F : List (WordTemplateLetter m),F.length ≤ L ∧ ∃ θ : WordParameter m (Fin n),
        C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      (wordPatternSet m L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  classical
  choose C hC htail using (fun F : List (WordTemplateLetter m)=>generalTemplateWord_gaussian_chaining f hR hj hA hD F)
  let G := wordPatternSet m L
  let T := 1+∑ F∈G,C F
  have hT : 0<T := by
    have hh : 0 ≤ ∑ F∈G,C F := Finset.sum_nonneg (fun F _=>(hC F).le)
    dsimp [T]
    linarith
  have hF (F : List (WordTemplateLetter m)) (hF : F∈G) : C F ≤ T := by
    have hh : C F ≤ ∑ F∈G,C F := Finset.single_le_sum (fun F _=>(hC F).le) hF
    dsimp [T]
    linarith
  refine ⟨T,hT,?_⟩
  intro n hn p
  let E : List (WordTemplateLetter m)→Set (MatrixCoordinates (Fin n)→ℝ) := fun F=>
    {g | ∃ θ : WordParameter m (Fin n),C F< matrixWordSeminorm p
      (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
        generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))}
  apply (measure_mono (show _⊆⋃ F∈G,E F from ?_)).trans
    ((measure_biUnion_finset_le G E).trans ?_)
  · intro g hg
    obtain ⟨F,hFl,θ,hθ⟩ := hg
    have hFm : F∈G := (mem_wordPatternSet F).mpr hFl
    exact mem_iUnion.mpr ⟨F,mem_iUnion.mpr ⟨hFm,θ,lt_of_le_of_lt (hF F hFm) hθ⟩⟩
  · calc
      _ ≤ ∑ F∈G,ENNReal.ofReal (3*exp (-(n:ℝ))) := Finset.sum_le_sum (fun F _=>htail F n hn p)
      _ = _ := by simp [G]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordTemplateSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*}

lemma inverseChart_exact {A : ℝ} (hA : 0<A) (a : ℝ) (ha : a∈Icc 0 A) :
    A*(inverseChart hA a ha:ℝ)=a := by
  dsimp [inverseChart]
  field_simp
lemma diagonalChart_exact {D : ℝ} (hD : 0<D) (d : ℝ) (hd : |d|≤D) :
    D*(2*(diagonalChart hD d hd:ℝ)-1)=d := by
  dsimp [diagonalChart]
  field_simp
  ring

lemma WordLetter.diagonalValue_bound {D : ℝ} (hD : 0≤D) (l : WordLetter ι)
    (hl : l.bounded D) (i : ι) : |l.diagonalValue i|≤D := by
  cases l with
  | diag d => exact hl i
  | noise => simpa [diagonalValue] using hD
  | inverse => simpa [diagonalValue] using hD

theorem templateWord_surjective {A D : ℝ} (hA : 0<A) (hD : 0<D)
    {a : ι→ℝ} (ha : ∀ i,a i∈Icc 0 A) (F : List (WordLetter ι))
    (hF : ∀ l∈F,l.bounded D) {L : ℕ} (hL : F.length≤L) :
    ∃ (G : List (WordTemplateLetter L)) (θ : WordParameter L ι),
      G.length=F.length ∧ templateInverse A θ=a ∧ templateWord D θ G=F := by
  classical
  let θ : WordParameter L ι := fun s=>match s.1 with
    | none => inverseChart hA (a s.2) (ha s.2)
    | some k => if hk : k.val<F.length then
        diagonalChart hD ((F[k.val]).diagonalValue s.2)
          (WordLetter.diagonalValue_bound hD.le _ (hF _ (List.getElem_mem hk)) _)
      else ⟨0,le_rfl,zero_le_one⟩
  let pattern : Fin F.length→WordTemplateLetter L := fun k=>match F[k.val] with
    | .diag _ => .diag ⟨k.val,lt_of_lt_of_le k.isLt hL⟩
    | .noise => .noise
    | .inverse => .inverse
  let G := List.ofFn pattern
  refine ⟨G,θ,by simp [G],?_,?_⟩
  · funext i
    exact inverseChart_exact hA (a i) (ha i)
  · have hp (k : Fin F.length) : (pattern k).realize D θ=F[k.val] := by
      cases hl : F[k.val] with
      | diag d =>
        dsimp [pattern]
        rw [hl]
        apply congrArg WordLetter.diag
        funext i
        simp only [templateDiagonal,θ,dite_eq_left k.isLt,hl,WordLetter.diagonalValue]
        exact diagonalChart_exact hD (d i) _
      | noise => simp [pattern,hl,WordTemplateLetter.realize]
      | inverse => simp [pattern,hl,WordTemplateLetter.realize]
    change (List.ofFn pattern).map (WordTemplateLetter.realize D θ)=F
    rw [List.map_ofFn]
    calc
      _ = List.ofFn (fun k : Fin F.length=>F[k.val]) := congrArg List.ofFn (funext hp)
      _ = F := List.ofFn_getElem
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem all_actualWords_gaussian_chaining_oai (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0<A) (hD : 0<D) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
        (∀ i,a i∈Icc 0 A) ∧ F.length ≤ L ∧ (∀ l∈F,l.bounded D) ∧
        C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  obtain ⟨C,hC,ht⟩ := all_generalTemplateWords_gaussian_chaining (m:=L) f hR hj hA.le hD.le L
  refine ⟨C,hC,?_⟩
  intro n hn p
  apply (measure_mono ?_).trans (ht n hn p)
  intro g hg
  obtain ⟨a,F,ha,hFL,hF,hg⟩ := hg
  obtain ⟨G,θ,hG,haθ,hFθ⟩ := templateWord_surjective hA hD ha F hF hFL
  refine ⟨G,by omega,θ,?_⟩
  simpa only [generalTemplateMatrix,haθ,hFθ] using hg
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.all_actualWords_gaussian_chaining_oai := @OAI.SKGap.all_actualWords_gaussian_chaining_oai
