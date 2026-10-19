-- Prove2me | solution 1 for OAI.ShiftedSections.adaptive_linear_equations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:22:41.985393+00:00
-- url     : https://prove2.me/submissions/4abc0e52-aa8b-4915-992b-35649c3131db

import Mathlib
import Definitions.Def_OAIQWESB000
import Theorems.Thm_ConvexOptimization_prekopa_leindler

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal Gaussian kernels and their densities. -/

section

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel

variable {ι : Type*} [Fintype ι]

lemma pi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (Measure.pi fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      ((show Integrable (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 (v i) (x i)) volume from
        by simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))).restrict)
      (ae_of_all _ fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i))),
    volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 (v i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (hv i) (s i)).symm

lemma diagonalLaw_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalLaw v = volume.withDensity (fun x => ENNReal.ofReal (density v x)) := by
  apply Measure.ext
  intro s hs
  rw [diagonalLaw, Measure.map_apply (PiLp.volume_preserving_toLp ι).measurable hs,
    pi_density v hv, withDensity_apply _ (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    ← lintegral_indicator hs]
  have he (x : ι → ℝ) :
      ((toLp 2) ⁻¹' s).indicator (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) x =
      s.indicator (fun x => ENNReal.ofReal (density v x)) (toLp 2 x) := by
    by_cases hx : toLp 2 x ∈ s <;> simp [hx, density]
  simp_rw [he]
  exact (PiLp.volume_preserving_toLp ι).lintegral_comp
    ((density_continuous v).measurable.ennreal_ofReal.indicator hs)

lemma density_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (x : EuclideanSpace ℝ ι) :
    0 < density v x := by
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 (v i) (x i) (hv i)

lemma density_neg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v (-x) = density v x := by
  unfold density
  apply Finset.prod_congr rfl
  intro i _
  simp [gaussianPDFReal]

section Scale
variable [DecidableEq ι]

lemma scaleMap_apply (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) (i : ι) :
    scaleMap v x i = Real.sqrt (v i : ℝ) * x i := by
  change (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ))).mulVec x.ofLp i = _
  simp only [Matrix.mulVec_diagonal]

lemma stdGaussian_map_scale (v : ι → ℝ≥0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v) = diagonalLaw v := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (scaleMap v).measurable
    (PiLp.volume_preserving_toLp ι).measurable]
  have he : (scaleMap v) ∘ (toLp 2) =
      (toLp 2) ∘ (fun x : ι → ℝ => fun i => Real.sqrt (v i : ℝ)*x i) := by
    ext x i
    exact scaleMap_apply v (toLp 2 x) i
  rw [he, ← Measure.map_map (PiLp.volume_preserving_toLp ι).measurable (by fun_prop),
    Measure.pi_map_pi (f := fun i (x : ℝ) => Real.sqrt (v i : ℝ)*x)
      (fun i => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  apply congrArg Measure.pi
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (v i).coe_nonneg]

end Scale

end GaussianKernel
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heat operators, weak coordinate derivatives, and Dirichlet energy. -/

section

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma inner_mulOp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f g : Lp ℂ 2 μ) :
    ⟪f, mulOp m hm hb g⟫ = ∫ x, m x * (g x * conj (f x)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulOp_coe m hm hb g] with x hx
  rw [hx]
  simp only [RCLike.inner_apply]
  ring

end Multiplier
end HeatL2

namespace HeatL2
section Translation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma translate_sub_norm_sq (a : E) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate a f - f‖^2 = ∫ ξ, ‖phase a ξ - 1‖^2 * ‖(𝓕 f) ξ‖^2 := by
  have hs : 𝓕 (translate a f - f) = 𝓕 (translate a f) - 𝓕 f :=
    (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _
  rw [← Lp.norm_fourier_eq (translate a f - f), hs, fourier_translate,
    norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (phaseOp a (𝓕 f)) (𝓕 f),
    phaseOp_coe a (𝓕 f)] with ξ h₁ h₂
  simp only [Pi.sub_apply] at h₁
  rw [h₁, h₂, ← sub_one_mul, norm_mul, mul_pow]

end Translation
end HeatL2

namespace HeatL2
section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_weight (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hb : ∀ᵐ x ∂volume, |m x| ≤ C) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun x => m x * ‖f x‖^2) := by
  apply Integrable.mono' (((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul C)
    (hm.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
  filter_upwards [hb] with x hx
  simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
    mul_le_mul_of_nonneg_right hx (sq_nonneg ‖f x‖)

lemma spectralOp_fourier (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    (fun x => (𝓕 (spectralOp m hm hb f) : Lp ℂ 2 (volume : Measure E)) x) =ᵐ[volume] fun x => (m x : ℂ) * (𝓕 f) x := by
  change ((Lp.fourierTransformₗᵢ E ℂ) ((Lp.fourierTransformₗᵢ E ℂ).symm _) : E → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact mulOp_coe (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) (C := 1)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)

lemma spectralOp_norm_le (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    ‖spectralOp m hm hb f‖ ≤ ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ E ℂ).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖mulOp (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)‖ ≤ ‖f‖
  exact (mulLp_norm_le (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) (C := 1)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)).trans_eq (by simp)

lemma spectralOp_inner (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    ⟪f, spectralOp m hm hb f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  have he : (fun x => inner ℂ ((𝓕 f) x) ((𝓕 (spectralOp m hm hb f)) x)) =ᵐ[volume]
      fun x => ((m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    filter_upwards [spectralOp_fourier m hm hb f] with x hx
    rw [hx]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, RCLike.mul_conj]
    simp
  rw [integral_congr_ae he, integral_complex_ofReal]

lemma spectralOp_positive (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (hn : ∀ x, 0 ≤ m x) :
    (spectralOp m hm hb).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have he : ⟪spectralOp m hm hb f, f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, spectralOp_inner]
    simp
  rw [he]
  exact ⟨rfl, integral_nonneg fun x => mul_nonneg (hn x) (sq_nonneg _)⟩

lemma heat_inner (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, heat w hw hn f⟫).re = ‖f‖^2 - energy w f := by
  rw [heat, spectralOp_inner]
  simp only [Complex.ofReal_re]
  have hb : ∀ x, |1-Real.exp (-w x)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x))))]
    linarith [Real.exp_pos (-w x)]
  have hint : Integrable (fun x => (1-Real.exp (-w x)) * ‖(𝓕 f) x‖^2) :=
    integrable_weight (fun x => 1-Real.exp (-w x))
      (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
      (Filter.Eventually.of_forall hb) (𝓕 f)
  rw [energy, ← Lp.norm_fourier_eq f, norm_sq_integral,
    ← integral_sub ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      hint]
  congr 1
  ext x
  ring

lemma energy_nonneg (w : E → ℝ) (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    0 ≤ energy w f := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))) (sq_nonneg _)

end Spectral
end HeatL2
namespace HeatL2

lemma loss_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ loss x := by
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))

lemma loss_le_one (x : ℝ) : loss x ≤ 1 := by
  unfold loss
  linarith [Real.exp_pos (-x)]

lemma loss_le_self (x : ℝ) : loss x ≤ x := by
  unfold loss
  linarith [Real.add_one_le_exp (-x)]

lemma loss_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    loss (x+y) ≤ loss x + loss y := by
  have hp := mul_nonneg (loss_nonneg hx) (loss_nonneg hy)
  simp only [loss, neg_add, Real.exp_add] at *
  nlinarith

lemma loss_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    loss (∑ i ∈ s, a i) ≤ ∑ i ∈ s, loss (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [loss]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (loss_add_le (ha i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj))).trans
      (add_le_add_right (ih fun j hj => ha j (Finset.mem_insert_of_mem hj)) _)

lemma loss_dilate_le {c x : ℝ} (hc : 1 ≤ c) : loss (c*x) ≤ c*loss x := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hci : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hci1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have he := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-c*x))
    (sub_nonneg.mpr hci1) hci.le (by ring : 1-c⁻¹+c⁻¹ = 1)
  have harg : (1-c⁻¹)*(0:ℝ) + c⁻¹*(-c*x) = -x := by field_simp; ring
  simp only [smul_eq_mul, harg, Real.exp_zero, mul_one] at he
  have hm := mul_le_mul_of_nonneg_left he hcpos.le
  rw [loss, loss]
  have hcc : c*c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
  simp only [mul_add, mul_sub, mul_one, ← mul_assoc, hcc, one_mul, neg_mul] at hm
  linarith

lemma loss_sum_dilate_le {ι : Type*} (s : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ s, 1 ≤ c i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    loss (∑ i ∈ s, c i*x i) ≤ ∑ i ∈ s, c i*loss (x i) := by
  exact (loss_sum_le s _ (fun i hi => mul_nonneg (le_trans zero_le_one (hc i hi)) (hx i hi))).trans
    (Finset.sum_le_sum fun i hi => loss_dilate_le (hc i hi))

lemma loss_mean_ge {ι : Type*} (s : Finset ι) (q x : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i = 1) :
    ∑ i ∈ s, q i*loss (x i) ≤ loss (∑ i ∈ s, q i*x i) := by
  have he := convexOn_exp.map_sum_le hq hs (fun i hi => Set.mem_univ (-x i))
  simp only [smul_eq_mul] at he
  have hneg : (∑ i ∈ s, q i * -x i) = -(∑ i ∈ s, q i*x i) := by simp [Finset.sum_neg_distrib]
  rw [hneg] at he
  simp only [loss, mul_sub, mul_one, Finset.sum_sub_distrib, hs]
  linarith

lemma loss_lower {x : ℝ} (hx : 0 ≤ x) : x/(1+x) ≤ loss x := by
  have hp : 0 < 1+x := by linarith
  have he : Real.exp (-x) ≤ (1+x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) hp).mpr (by linarith [Real.add_one_le_exp x])
  rw [loss, div_le_iff₀ hp]
  have hmul := mul_le_mul_of_nonneg_right he hp.le
  rw [inv_mul_cancel₀ hp.ne'] at hmul
  nlinarith

lemma bound_by_loss {A H η z : ℝ} (hH : 0 ≤ H) (hη : 0 < η)
    (hz : 0 ≤ z) (h₁ : A ≤ H*z) (h₂ : A ≤ 4) :
    A ≤ (H+4*η)/η * loss (η*z) := by
  have hp : 0 < 1+η*z := by positivity
  have hlow := loss_lower (mul_nonneg hη.le hz)
  have hc : 0 ≤ (H+4*η)/η := by positivity
  have he : A ≤ (H+4*η)/η * (η*z/(1+η*z)) := by
    have hr : (H+4*η)/η * (η*z/(1+η*z)) = (H*z+4*η*z)/(1+η*z) := by
      field_simp
    rw [hr, le_div_iff₀ hp]
    have hm := mul_le_mul_of_nonneg_right h₂ (mul_nonneg hη.le hz)
    nlinarith
  exact he.trans (mul_le_mul_of_nonneg_left hlow hc)

end HeatL2

namespace HeatL2
section Mask
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mask_coe (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    (mask D hD f : X → ℂ) =ᵐ[μ] D.indicator f := by
  filter_upwards [mulOp_coe (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f] with x hx
  change mulOp _ _ _ f x = _
  rw [hx]
  classical
  by_cases hx : x ∈ D <;> simp [hx]

lemma mask_norm_le (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    ‖mask D hD f‖ ≤ ‖f‖ := by
  apply le_trans (mulLp_norm_le (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f)
  simp only [one_mul, le_refl]

lemma mask_idempotent (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD (mask D hD f) = mask D hD f := by
  apply Lp.ext
  filter_upwards [mask_coe D hD (mask D hD f), mask_coe D hD f] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp_all

lemma mask_inner (D : Set X) (hD : MeasurableSet D) (f g : Lp ℂ 2 μ) :
    ⟪mask D hD f, g⟫ = ⟪f, mask D hD g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mask_coe D hD f, mask_coe D hD g] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp [h₁, h₂, hx]

lemma mask_adjoint (D : Set X) (hD : MeasurableSet D) :
    (mask (μ := μ) D hD).adjoint = mask D hD := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (mask_inner D hD f g).symm

lemma mask_eq_self_iff (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD f = f ↔ f ∈ supported D := by
  classical
  constructor
  · intro h
    have hc := mask_coe D hD f
    rw [h] at hc
    filter_upwards [hc] with x hx hnot
    simpa [hnot] using hx
  · intro h
    apply Lp.ext
    filter_upwards [mask_coe D hD f, h] with x hx hs
    by_cases hmem : x ∈ D <;> simp [hx, hmem, hs]

end Mask

section PositiveNorm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma positive_norm_le_iff (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ} (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ f, (⟪f, T f⟫).re ≤ C * ‖f‖^2 := by
  constructor
  · intro h f
    have he := (Complex.re_le_norm ⟪f, T f⟫).trans (norm_inner_le_norm f (T f))
    have hn := T.le_opNorm f
    have hm := mul_le_mul_of_nonneg_left (hn.trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg f))) (norm_nonneg f)
    nlinarith
  · intro h
    rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
    apply ciSup_le
    intro f
    have hre : (⟪T f, f⟫).re = (⟪f, T f⟫).re := inner_re_symm (𝕜 := ℂ) (T f) f
    change |(⟪T f, f⟫).re / ‖f‖^2| ≤ C
    have hnon : 0 ≤ (⟪T f, f⟫).re := hT.re_inner_nonneg_left f
    rw [abs_of_nonneg (div_nonneg hnon (sq_nonneg _)), hre]
    by_cases hf : f = 0
    · simpa [hf] using hC
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (h f)

lemma positive_exists_form_gt (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ}
    (hC : 0 ≤ C) (h : C < ‖T‖) : ∃ f, C * ‖f‖^2 < (⟪f, T f⟫).re := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) ((positive_norm_le_iff T hT hC).mpr hn)

end PositiveNorm

section Compressed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma heat_positive (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (heat w hw hn).IsPositive := spectralOp_positive _ _ _ (fun _ => (Real.exp_pos _).le)

lemma compressedHeat_positive (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (compressedHeat D hD w hw hn).IsPositive := by
  have hp := (heat_positive w hw hn).adjoint_conj (mask D hD)
  rwa [mask_adjoint] at hp

lemma compressedHeat_inner (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, compressedHeat D hD w hw hn f⟫).re =
      ‖mask D hD f‖^2 - energy w (mask D hD f) := by
  change (⟪f, mask D hD (heat w hw hn (mask D hD f))⟫).re = _
  rw [← mask_inner, heat_inner]

lemma compressedHeat_norm_le_one (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    ‖compressedHeat D hD w hw hn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖mask D hD (heat w hw hn (mask D hD f))‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact (mask_norm_le _ _ _).trans ((spectralOp_norm_le _ _ _ _).trans (mask_norm_le _ _ _))

end Compressed
end HeatL2

namespace HeatL2
section Average
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma average_apply (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : average A ν f = ∫ z, translate (A z) f ∂ν := rfl

lemma inner_average (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ ξ, (∫ z, phase (A z) ξ ∂ν) * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  have hp : Integrable (fun ξ => (𝓕 f) ξ * conj ((𝓕 g) ξ)) (volume : Measure E) := by
    simpa only [RCLike.inner_apply] using L2.integrable_inner (𝕜 := ℂ) (𝓕 g) (𝓕 f)
  have hm : Continuous (fun p : F × E => phase (A p.1) p.2) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((A.continuous.comp continuous_fst).inner continuous_snd)
  have hi : Integrable (fun p : F × E => phase (A p.1) p.2 *
      ((𝓕 f) p.2 * conj ((𝓕 g) p.2))) (ν.prod volume) := by
    apply Integrable.mono' (hp.norm.comp_snd ν) (hm.aestronglyMeasurable.mul hp.aestronglyMeasurable.comp_snd)
    exact Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply, norm_mul, phase_norm, one_mul, le_refl]
  have hinner (z : F) : ⟪g, translate (A z) f⟫ =
      ∫ ξ, phase (A z) ξ * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
    rw [← Lp.inner_fourier_eq, fourier_translate]
    exact inner_mulOp _ _ _ _ _
  simp_rw [hinner]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => integral_mul_const _ _

omit [MeasurableSpace E] [BorelSpace E] in
lemma integral_phase_gaussian (A : F →L[ℝ] E) (ξ : E) :
    (∫ z, phase (A z) ξ ∂ProbabilityTheory.stdGaussian F) =
      (Real.exp (-gaussianSymbol A ξ) : ℂ) := by
  have he := ProbabilityTheory.charFun_stdGaussian ((2*Real.pi) • A.adjoint ξ)
  rw [charFun_apply] at he
  have hf : (fun z => phase (A z) ξ) = fun z =>
      Complex.exp ((inner ℝ z ((2*Real.pi) • A.adjoint ξ) : ℂ) * Complex.I) := by
    ext z
    rw [phase, Real.fourierChar_apply, inner_smul_right, A.adjoint_inner_right]
  rw [hf, he, gaussianSymbol, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma average_gaussian_eq_heat (A : F →L[ℝ] E) :
    average A (ProbabilityTheory.stdGaussian F) =
      heat (gaussianSymbol A) (gaussianSymbol_continuous A).aestronglyMeasurable
        (gaussianSymbol_nonneg A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [inner_average]
  simp_rw [integral_phase_gaussian]
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  apply integral_congr_ae
  have hb : ∀ ξ, |Real.exp (-gaussianSymbol A ξ)| ≤ 1 := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (gaussianSymbol_nonneg A ξ))
  filter_upwards [spectralOp_fourier (fun ξ => Real.exp (-gaussianSymbol A ξ))
    (Real.continuous_exp.comp_aestronglyMeasurable (gaussianSymbol_continuous A).aestronglyMeasurable.neg)
    hb f] with ξ hξ
  change _ = inner ℂ ((𝓕 g) ξ) ((𝓕 (heat _ _ _ f)) ξ)
  rw [heat, hξ]
  simp only [RCLike.inner_apply]
  ring

end Average
end HeatL2

namespace HeatL2
section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_energy (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun ξ => loss (w ξ) * ‖(𝓕 f) ξ‖^2) := by
  apply integrable_weight (fun ξ => loss (w ξ))
    (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
    (C := 1) _ (𝓕 f)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [abs_of_nonneg (loss_nonneg (hn ξ))]
    exact loss_le_one _

lemma energy_le_norm_sq (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) : energy w f ≤ ‖f‖^2 := by
  rw [← Lp.norm_fourier_eq f, norm_sq_integral]
  apply integral_mono (integrable_energy w hw hn f)
    ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
  intro ξ
  exact mul_le_of_le_one_left (sq_nonneg _) (loss_le_one _)

lemma energy_mean_ge {ι : Type*} (s : Finset ι) (q : ι → ℝ) (w : ι → E → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i = 1)
    (hw : ∀ i ∈ s, AEStronglyMeasurable (w i) volume)
    (hn : ∀ i ∈ s, ∀ ξ, 0 ≤ w i ξ) (f : Lp ℂ 2 (volume : Measure E)) :
    ∑ i ∈ s, q i * energy (w i) f ≤ energy (fun ξ => ∑ i ∈ s, q i * w i ξ) f := by
  have hi i (h : i ∈ s) := (integrable_energy (w i) (hw i h) (hn i h) f).const_mul (q i)
  have hw' : AEStronglyMeasurable (fun ξ => ∑ i ∈ s, q i * w i ξ) volume := by
    exact s.aestronglyMeasurable_fun_sum fun i hi => (hw i hi).const_mul (q i)
  have hn' ξ : 0 ≤ ∑ i ∈ s, q i * w i ξ := Finset.sum_nonneg fun i hi => mul_nonneg (hq i hi) (hn i hi ξ)
  have he : (∑ i ∈ s, q i * energy (w i) f) = ∫ ξ, ∑ i ∈ s, q i * (loss (w i ξ) * ‖(𝓕 f) ξ‖^2) := by
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  rw [he]
  apply integral_mono (integrable_finsetSum s hi) (integrable_energy _ hw' hn' f)
  intro ξ
  simpa only [← mul_assoc, ← Finset.sum_mul] using
    mul_le_mul_of_nonneg_right (loss_mean_ge s q (fun i => w i ξ) hq hs) (sq_nonneg ‖(𝓕 f) ξ‖)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma directionalSymbol_nonneg (e ξ : E) : 0 ≤ directionalSymbol e ξ := sq_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma directionalSymbol_continuous (e : E) : Continuous (directionalSymbol e) := by
  unfold directionalSymbol
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_one_sq_le (e ξ : E) (h : ℝ) :
    ‖phase (h • e) ξ - 1‖^2 ≤ h^2 * directionalSymbol e ξ := by
  have hb : ‖phase (h • e) ξ - 1‖ ≤ ‖2*Real.pi*inner ℝ (h • e) ξ‖ := by
    rw [phase, Real.fourierChar_apply, mul_comm _ Complex.I]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb
  have he : ‖2*Real.pi*inner ℝ (h • e) ξ‖^2 = h^2 * directionalSymbol e ξ := by
    simp only [inner_smul_left, starRingEnd_apply, star_trivial,
      Real.norm_eq_abs, sq_abs, directionalSymbol]
    ring
  exact hs.trans_eq he

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_one_sq_le_four (a ξ : E) : ‖phase a ξ - 1‖^2 ≤ 4 := by
  have hn : ‖phase a ξ - 1‖ ≤ 2 := by
    simpa only [phase_norm, norm_one, one_add_one_eq_two] using norm_sub_le (phase a ξ) (1:ℂ)
  nlinarith [norm_nonneg (phase a ξ - 1)]

lemma directional_translate_bound (e : E) (h η : ℝ) (hη : 0 < η)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ‖translate (h • e) f - f‖^2 ≤ (h^2 + 4*η)/η * energy (fun ξ => η * directionalSymbol e ξ) f := by
  rw [translate_sub_norm_sq, energy, ← integral_const_mul]
  have hw : AEStronglyMeasurable (fun ξ => η * directionalSymbol e ξ) volume :=
    ((directionalSymbol_continuous e).const_mul η).aestronglyMeasurable
  have hn ξ := mul_nonneg hη.le (directionalSymbol_nonneg e ξ)
  have hleft : Integrable (fun ξ => ‖phase (h • e) ξ - 1‖^2 * ‖(𝓕 f) ξ‖^2) := by
    apply integrable_weight (fun ξ => ‖phase (h • e) ξ - 1‖^2)
      (((phase_continuous _).sub continuous_const).norm.pow 2).aestronglyMeasurable
      (C := 4) _ (𝓕 f)
    exact Filter.Eventually.of_forall fun ξ => by
      simpa only [abs_pow, abs_norm] using phase_sub_one_sq_le_four (h • e) ξ
  apply integral_mono hleft ((integrable_energy _ hw hn f).const_mul _)
  intro ξ
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (bound_by_loss (sq_nonneg h) hη (directionalSymbol_nonneg e ξ)
      (phase_sub_one_sq_le e ξ h) (phase_sub_one_sq_le_four (h • e) ξ)) (sq_nonneg ‖(𝓕 f) ξ‖)

end Energy
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

lemma sqrt_pair_sub_sq_le (a b c d : ℝ) :
    (Real.sqrt (a^2+b^2) - Real.sqrt (c^2+d^2))^2 ≤ (a-c)^2+(b-d)^2 := by
  have hx : 0 ≤ a^2+b^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy : 0 ≤ c^2+d^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : (a*c+b*d)^2 ≤ (a^2+b^2)*(c^2+d^2) := by
    nlinarith [sq_nonneg (a*d-b*c)]
  have hp : (a^2+b^2)*(c^2+d^2) =
      (Real.sqrt (a^2+b^2)*Real.sqrt (c^2+d^2))^2 := by
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hcs : a*c+b*d ≤ Real.sqrt (a^2+b^2)*Real.sqrt (c^2+d^2) := by
    rw [hp] at hs
    nlinarith [mul_nonneg (Real.sqrt_nonneg (a^2+b^2)) (Real.sqrt_nonneg (c^2+d^2))]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma sqrt_mix_sub_sq_le (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (a b c d : ℝ) :
    (Real.sqrt (t*a^2+u*b^2) - Real.sqrt (t*c^2+u*d^2))^2 ≤ t*(a-c)^2+u*(b-d)^2 := by
  have he (x y : ℝ) : (Real.sqrt t*x)^2+(Real.sqrt u*y)^2=t*x^2+u*y^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hu]
  have h := sqrt_pair_sub_sq_le (Real.sqrt t*a) (Real.sqrt u*b) (Real.sqrt t*c) (Real.sqrt u*d)
  rw [he, he] at h
  have hr : (Real.sqrt t*a-Real.sqrt t*c)^2+(Real.sqrt u*b-Real.sqrt u*d)^2=
      t*(a-c)^2+u*(b-d)^2 := by
    rw [← mul_sub, ← mul_sub, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hu]
  exact h.trans_eq hr

section Mixture
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mixture_coe (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    (mixture t ht ht' f g : X → ℂ) =ᵐ[μ] mixFun t f g := MemLp.coeFn_toLp _

lemma mixFun_norm_sq (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) (x : X) :
    ‖mixFun t f g x‖^2 = t*‖f x‖^2+(1-t)*‖g x‖^2 := by
  rw [mixFun, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt]
  positivity

lemma mixture_norm_sq (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) :
    ‖mixture t ht ht' f g‖^2 = t*‖f‖^2+(1-t)*‖g‖^2 := by
  rw [norm_sq_integral, norm_sq_integral f, norm_sq_integral g]
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hg := (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul t) (hg.const_mul (1-t))]
  apply integral_congr_ae
  filter_upwards [mixture_coe t ht ht' f g] with x hx
  rw [hx, mixFun_norm_sq t ht ht']

lemma mixFun_sub_sq_le (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) (f g : Lp ℂ 2 μ) (x y : X) :
    ‖mixFun t f g x - mixFun t f g y‖^2 ≤ t*‖f x-f y‖^2+(1-t)*‖g x-g y‖^2 := by
  have hu := sub_nonneg.mpr ht'
  have hb := sqrt_mix_sub_sq_le t (1-t) ht hu ‖f x‖ ‖g x‖ ‖f y‖ ‖g y‖
  have h₁ : (‖f x‖-‖f y‖)^2 ≤ ‖f x-f y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.mpr (abs_norm_sub_norm_le (f x) (f y)))
  have h₂ : (‖g x‖-‖g y‖)^2 ≤ ‖g x-g y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.mpr (abs_norm_sub_norm_le (g x) (g y)))
  have h := hb.trans (add_le_add (mul_le_mul_of_nonneg_left h₁ ht) (mul_le_mul_of_nonneg_left h₂ hu))
  simpa only [mixFun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

lemma mixture_supported (D : Set X) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 μ) (hf : f ∈ supported D) (hg : g ∈ supported D) :
    mixture t ht ht' f g ∈ supported D := by
  change ∀ᵐ x ∂μ, x ∉ D → mixture t ht ht' f g x = 0
  filter_upwards [mixture_coe t ht ht' f g, hf, hg] with x hx hf hg hnot
  simp only [hx, mixFun, hf hnot, hg hnot, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Real.sqrt_zero, Complex.ofReal_zero]

end Mixture

section MixtureTranslation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma mixture_translation_sq_le (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure E)) (a : E) :
    ‖translate a (mixture t ht ht' f g) - mixture t ht ht' f g‖^2 ≤
      t * ‖translate a f - f‖^2 + (1-t) * ‖translate a g - g‖^2 := by
  rw [norm_sq_integral, norm_sq_integral (translate a f - f), norm_sq_integral (translate a g - g)]
  have hf := (Lp.memLp (translate a f - f)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hg := (Lp.memLp (translate a g - g)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul t) (hg.const_mul (1-t))]
  apply integral_mono_ae
    ((Lp.memLp _).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((hf.const_mul t).add (hg.const_mul (1-t)))
  have hm := mixture_coe t ht ht' f g
  have hma := (measurePreserving_add_right (volume : Measure E) a).quasiMeasurePreserving.ae_eq_comp hm
  filter_upwards [hm, hma, translate_coe a (mixture t ht ht' f g), translate_coe a f,
    translate_coe a g, Lp.coeFn_sub (translate a (mixture t ht ht' f g)) (mixture t ht ht' f g),
    Lp.coeFn_sub (translate a f) f, Lp.coeFn_sub (translate a g) g] with x hm hma hb hf hg hc hd he
  simp only [Pi.sub_apply] at hc hd he
  change mixture t ht ht' f g (x+a) = mixFun t f g (x+a) at hma
  simp only [Pi.add_apply]
  rw [hc, hb, hma, hm, hd, he, hf, hg]
  exact mixFun_sub_sq_le t ht ht' f g (x+a) x

end MixtureTranslation
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2
section Difference
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in
lemma integrable_difference_sq (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun z => ‖translate (A z) f - f‖^2) ν := by
  apply Integrable.mono' (integrable_const (4 * ‖f‖^2))
    ((((translate_continuous f).comp A.continuous).sub continuous_const).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_sub_le (translate (A z) f) f
    rw [(translate (A z)).norm_map] at h
    change ‖translate (A z) f - f‖^2 ≤ 4 * ‖f‖^2
    nlinarith [norm_nonneg (translate (A z) f - f)]

lemma average_difference_sq (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) :
    (∫ z, ‖translate (A z) f - f‖^2 ∂ν) = 2 * (‖f‖^2 - (⟪f, average A ν f⟫).re) := by
  have hi : Integrable (fun z => (⟪f, translate (A z) f⟫).re) ν :=
    ((integrable_translate A ν f).const_inner (𝕜 := ℂ) f).re
  have he z : ‖translate (A z) f - f‖^2 =
      ‖f‖^2 - 2 * (⟪f, translate (A z) f⟫).re + ‖f‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ), (translate (A z)).norm_map, inner_re_symm (𝕜 := ℂ)]
    rfl
  simp_rw [he]
  have hi' : Integrable (fun z => ‖f‖^2 - 2 * (⟪f, translate (A z) f⟫).re) ν :=
    (integrable_const (‖f‖^2)).sub (hi.const_mul 2)
  have hr := integral_re ((integrable_translate A ν f).const_inner (𝕜 := ℂ) f)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [integral_add hi' (integrable_const (‖f‖^2)),
    integral_sub (integrable_const (‖f‖^2)) (hi.const_mul 2), integral_const_mul,
    integral_const, probReal_univ, one_smul, hr,
    integral_inner (integrable_translate A ν f), ← average_apply]
  ring

lemma gaussian_energy_difference (A : F →L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    energy (gaussianSymbol A) f = (1/2:ℝ) *
      ∫ z, ‖translate (A z) f - f‖^2 ∂ProbabilityTheory.stdGaussian F := by
  rw [average_difference_sq, average_gaussian_eq_heat, heat_inner]
  ring

end Difference
end HeatL2

lemma selfAdjoint_norm_pow {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (a : A) (ha : IsSelfAdjoint a) (n : ℕ) (hn : n ≠ 0) : ‖a^n‖ = ‖a‖^n := by
  by_cases hz : a = 0
  · simp [hz, zero_pow hn]
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hlarge : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self (n := n))
  have hrem : 2^n-n ≠ 0 := Nat.ne_zero_of_lt (Nat.sub_pos_of_lt (Nat.lt_two_pow_self (n := n)))
  have he : n + (2^n-n) = 2^n := Nat.add_sub_of_le hlarge
  have h : ‖a‖^n * ‖a‖^(2^n-n) ≤ ‖a^n‖ * ‖a‖^(2^n-n) := by
    calc
      _ = ‖a‖^(2^n) := by rw [← pow_add, he]
      _ = ‖a^(2^n)‖ := (ha.norm_pow_two_pow n).symm
      _ = ‖a^n * a^(2^n-n)‖ := by rw [← pow_add, he]
      _ ≤ ‖a^n‖ * ‖a^(2^n-n)‖ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pow_le' _ (Nat.pos_of_ne_zero hrem)) (norm_nonneg _)
  exact le_antisymm (norm_pow_le' _ (Nat.pos_of_ne_zero hn)) ((mul_le_mul_iff_left₀ (pow_pos hp _)).mp h)

open MeasureTheory Filter ComplexConjugate
open scoped ComplexInnerProductSpace ENNReal

namespace HeatL2

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

lemma kernelOp_coe (f : Lp ℂ 2 μ) : (kernelOp k f : X → ℂ) =ᵐ[μ] kernelFun k f := kernelLp_coe k f

lemma inner_one_eq_integral (f : Lp ℂ 2 μ) :
    ⟪(oneLp : Lp ℂ 2 μ), f⟫ = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneLp_coe (μ := μ)] with x hx
  simp only [hx, RCLike.inner_apply, map_one, mul_one]

lemma kernelFun_domination (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) (x : X) :
    ‖kernelFun k f x‖ ≤ (kernelFun k g x).re := by
  unfold kernelFun
  have hr := integral_re (kernel_section_integrable k g x)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [← hr]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (kernel_section_integrable k f x).norm
    (kernel_section_integrable k g x).re
  filter_upwards [hfg] with y hy
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (k.nonneg _), RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hy (k.nonneg _)

lemma kernelOp_domination (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) :
    ∀ᵐ x ∂μ, ‖kernelOp k f x‖ ≤ (kernelOp k g x).re := by
  filter_upwards [kernelOp_coe k f, kernelOp_coe k g] with x hf hg
  rw [hf, hg]
  exact kernelFun_domination k f g hfg x

lemma kernel_pow_domination (n : ℕ) (f g : Lp ℂ 2 μ)
    (hfg : ∀ᵐ y ∂μ, ‖f y‖ ≤ (g y).re) :
    ∀ᵐ x ∂μ, ‖(kernelOp k ^ n) f x‖ ≤ ((kernelOp k ^ n) g x).re := by
  induction n with
  | zero => simpa using hfg
  | succ n hn =>
    simpa only [pow_succ', mul_apply_eq_comp] using kernelOp_domination k _ _ hn

lemma kernel_norm_le_integral (f : Lp ℂ 2 μ) :
    ‖kernelOp k f‖ ≤ k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * (∫ x, ‖f x‖ ∂μ) := by
  have h : ‖kernelOp k f‖ ≤ (k.bound * ∫ x, ‖f x‖ ∂μ) * ‖(oneLp : Lp ℂ 2 μ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [kernelOp_coe k f, oneLp_coe (μ := μ)] with x hx ho
    rw [hx, ho, norm_one, mul_one]
    exact kernelFun_bound k f x
  nlinarith [h]

lemma pathMass_eq_integral (n : ℕ) :
    pathMass (μ := μ) k n = ∫ x, (((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ)) x).re ∂μ := by
  rw [pathMass, inner_one_eq_integral]
  have hr := integral_re ((Lp.memLp ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))).integrable (by norm_num))
  simpa only [RCLike.re_eq_complex_re] using hr.symm

lemma pathMass_nonneg (n : ℕ) : 0 ≤ pathMass (μ := μ) k n := by
  rw [pathMass_eq_integral]
  apply integral_nonneg_of_ae
  have h : ∀ᵐ x ∂μ, ‖(0 : Lp ℂ 2 μ) x‖ ≤ ((oneLp : Lp ℂ 2 μ) x).re := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ, oneLp_coe (μ := μ)] with x hz ho
    simp only [Pi.zero_apply] at hz
    rw [hz, ho]
    norm_num
  have hd := kernel_pow_domination k n 0 oneLp h
  simp only [map_zero] at hd
  filter_upwards [hd, Lp.coeFn_zero ℂ 2 μ] with x hx hz
  simp only [Pi.zero_apply] at hz
  rwa [hz, norm_zero] at hx

lemma pathMass_le (n : ℕ) :
    pathMass (μ := μ) k n ≤ ‖(oneLp : Lp ℂ 2 μ)‖^2 * ‖(kernelOp (μ := μ) k)‖^n := by
  unfold pathMass
  calc
    _ ≤ ‖⟪(oneLp : Lp ℂ 2 μ), (kernelOp k ^ n) oneLp⟫‖ := Complex.re_le_norm _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖(kernelOp k ^ n) oneLp‖ := norm_inner_le_norm _ _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp k ^ n : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ * ‖(oneLp : Lp ℂ 2 μ)‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp (μ := μ) k)‖^n * ‖(oneLp : Lp ℂ 2 μ)‖) := by
      gcongr
      rcases n with _ | n
      · exact ContinuousLinearMap.norm_id_le
      · exact norm_pow_le' _ (Nat.succ_pos _)
    _ = _ := by ring

lemma kernel_pow_norm_le_pathMass (n : ℕ) :
    ‖(kernelOp (μ := μ) k ^ (n+2))‖ ≤
      k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2 * pathMass (μ := μ) k n := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (pathMass_nonneg k n)
  intro f
  let C := k.bound * ‖(oneLp : Lp ℂ 2 μ)‖ * ‖f‖
  have hf : ∀ᵐ x ∂μ, ‖kernelOp k f x‖ ≤ (((C : ℂ) • (oneLp : Lp ℂ 2 μ)) x).re := by
    filter_upwards [kernelOp_coe k f, oneLp_coe (μ := μ),
      Lp.coeFn_smul (C : ℂ) (oneLp : Lp ℂ 2 μ)] with x hx ho hs
    rw [hx, hs]
    simp only [Pi.smul_apply, smul_eq_mul, ho, mul_one, Complex.ofReal_re]
    exact kernelFun_norm_bound k f x
  have hd := kernel_pow_domination k n _ _ hf
  rw [map_smul] at hd
  have hi : (∫ x, ‖(kernelOp k ^ n) (kernelOp k f) x‖ ∂μ) ≤
      C * pathMass (μ := μ) k n := by
    rw [pathMass_eq_integral, ← integral_const_mul]
    have hrg : Integrable (fun x => (((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ)) x).re) μ := by
      simpa only [RCLike.re_eq_complex_re] using
        ((Lp.memLp ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))).integrable (by norm_num)).re
    apply integral_mono_ae ((Lp.memLp ((kernelOp k ^ n) (kernelOp k f))).integrable (by norm_num)).norm
      (hrg.const_mul C)
    filter_upwards [hd, Lp.coeFn_smul (C : ℂ) ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))] with x hx hs
    rw [hs] at hx
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hx
  have he : (kernelOp k ^ (n+2)) f = kernelOp k ((kernelOp k ^ n) (kernelOp k f)) := by
    rw [show n+2 = (n+1)+1 by omega, pow_succ', pow_succ,
      mul_apply_eq_comp, mul_apply_eq_comp]
  rw [he]
  apply (kernel_norm_le_integral k _).trans
  apply (mul_le_mul_of_nonneg_left hi (mul_nonneg k.bound_nonneg (norm_nonneg _))).trans
  exact le_of_eq (by dsimp [C]; ring)

lemma kernel_pair_integrable (f g : Lp ℂ 2 μ) :
    Integrable (fun p : X × X => (k.value p : ℂ) * g p.2 * conj (f p.1)) (μ.prod μ) := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
  have hg := ((Lp.memLp g).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
  apply Integrable.mono' ((hf.mul_prod hg).const_mul k.bound)
    (((Complex.continuous_ofReal.comp_aestronglyMeasurable k.measurable.aestronglyMeasurable).mul
      (Lp.memLp g).aestronglyMeasurable.comp_snd).mul
        (continuous_star.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable.comp_fst))
  exact Filter.Eventually.of_forall fun p => by
    change ‖(k.value p : ℂ) * g p.2 * conj (f p.1)‖ ≤ k.bound * (‖f p.1‖ * ‖g p.2‖)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (k.nonneg _), Complex.norm_conj]
    calc
      _ ≤ k.bound * ‖g p.2‖ * ‖f p.1‖ := by gcongr; exact k.le_bound p
      _ = _ := by ring

lemma inner_kernel (f g : Lp ℂ 2 μ) :
    ⟪f, kernelOp k g⟫ = ∫ x, ∫ y, (k.value (x,y) : ℂ) * g y * conj (f x) ∂μ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelOp_coe k g] with x hx
  simp only [RCLike.inner_apply, hx, kernelFun, integral_mul_const]

lemma kernelOp_selfAdjoint (hs : ∀ x y, k.value (x,y) = k.value (y,x)) :
    IsSelfAdjoint (kernelOp (μ := μ) k) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪kernelOp k f, g⟫ = ⟪f, kernelOp k g⟫
  rw [← inner_conj_symm, inner_kernel, ← integral_conj]
  simp_rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  conv_rhs => rw [inner_kernel, integral_integral_swap (kernel_pair_integrable k f g)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun y => by dsimp only; rw [hs x y]; ring)

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace

namespace HeatL2

lemma le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^n ≤ C*b^n) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have ha' : 0 < a := hb.trans_lt hab
  have hr : b/a < 1 := (div_lt_one ha').mpr hab
  have ht : Tendsto (fun n : ℕ => C*(b/a)^n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb ha) hr)
  have hh (n : ℕ) : 1 ≤ C*(b/a)^n := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos ha' n)]
    simpa only [one_mul] using h n
  have := ge_of_tendsto' ht hh
  linarith

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

lemma kernel_norm_pow_le_pathMass (hs : ∀ x y, k.value (x,y) = k.value (y,x)) (n : ℕ) :
    ‖kernelOp (μ := μ) k‖^(n+2) ≤
      k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2 * pathMass (μ := μ) k n := by
  rw [← selfAdjoint_norm_pow _ (kernelOp_selfAdjoint k hs) (n+2) (by omega)]
  exact kernel_pow_norm_le_pathMass k n

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ComplexInnerProductSpace ENNReal
namespace HeatL2
section Restrict
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (D : Set X) (hD : MeasurableSet D)
lemma extendLp_coe (f : Lp ℂ 2 (μ.restrict D)) :
    (extendLp D hD f : X → ℂ) =ᵐ[μ] D.indicator f := MemLp.coeFn_toLp _
lemma extendLp_norm (f : Lp ℂ 2 (μ.restrict D)) : ‖extendLp D hD f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (extendLp_coe D hD f), eLpNorm_indicator_eq_eLpNorm_restrict hD]
lemma extendLp_supported (f : Lp ℂ 2 (μ.restrict D)) : extendLp D hD f ∈ supported D := by
  filter_upwards [extendLp_coe D hD f] with x hx hnot
  simp [hx, hnot]
lemma restrictLp_coe (f : Lp ℂ 2 μ) :
    (restrictLp D f : X → ℂ) =ᵐ[μ.restrict D] f := MemLp.coeFn_toLp _
lemma extend_restrict (f : Lp ℂ 2 μ) : extendLp D hD (restrictLp D f) = mask D hD f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hD).mp (restrictLp_coe D f)
  filter_upwards [extendLp_coe D hD (restrictLp D f), mask_coe D hD f, hr] with x h₁ h₂ h₃
  rw [h₁,h₂]
  by_cases hx : x ∈ D
  · simpa only [Set.indicator_of_mem hx] using h₃ hx
  · simp [hx]
end Restrict
end HeatL2

open MeasureTheory FourierTransform Filter Set
open scoped ComplexInnerProductSpace
namespace HeatL2

lemma weighted_rpow_jensen {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g v : X → ℝ} (hg : Measurable g) (hgi : Integrable g μ)
    (hgn : ∀ x, 0 ≤ g x) (hg1 : ∫ x, g x ∂μ = 1)
    (hv : Measurable v) (hv01 : ∀ x, v x ∈ Icc (0:ℝ) 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, v x * g x ∂μ)^p ≤ ∫ x, (v x)^p * g x ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have : IsProbabilityMeasure ν := by
    apply isProbabilityMeasure_iff.mpr
    change μ.withDensity (fun x => ENNReal.ofReal (g x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn), hg1]
    norm_num
  have he (f : X → ℝ) : (∫ x, f x ∂ν) = ∫ x, f x * g x ∂μ := by
    change (∫ x, f x ∂(μ.withDensity (fun x => ENNReal.ofReal (g x)))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f]
    simp only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul, mul_comm (g _)]
  have hcont : Continuous (fun x : ℝ => x^p) := Real.continuous_rpow_const (by positivity)
  have hi : Integrable v ν := Integrable.of_bound hv.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hv01 x).1]; exact (hv01 x).2)
  have hip : Integrable (fun x => (v x)^p) ν := Integrable.of_bound
    (hcont.measurable.comp hv).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hv01 x).1 _)]
      exact Real.rpow_le_one (hv01 x).1 (hv01 x).2 (by linarith))
  have h := (convexOn_rpow hp).map_integral_le hcont.continuousOn isClosed_Ici
    (ae_of_all ν fun x => (hv01 x).1) hi hip
  simpa only [Pi.neg_apply, he] using h

section Form
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma heat_inner_integral (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, heat w hw hn f⟫).re = ∫ ξ, Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2 := by
  rw [heat, spectralOp_inner]
  rfl

lemma heat_form_rpow (w : E → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    {t η : ℝ} (hη : 0 < η) (hηt : η ≤ t)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : ‖f‖ = 1) :
    ((⟪f, heat (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ)) f⟫).re) ^ (t/η) ≤
    (⟪f, heat (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ)) f⟫).re := by
  simp only [heat_inner_integral]
  have hg1 : (∫ ξ, ‖(𝓕 f) ξ‖^2) = 1 := by
    rw [← norm_sq_integral, Lp.norm_fourier_eq, hf, one_pow]
  have h := weighted_rpow_jensen
    ((Lp.stronglyMeasurable (𝓕 f)).measurable.norm.pow_const 2)
    ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    (fun _ => sq_nonneg _) hg1 ((hw.const_mul η).neg.exp)
    (fun ξ => ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hη.le (hn ξ)))⟩)
    ((one_le_div hη).mpr hηt)
  have he (ξ : E) : Real.exp (-(η*w ξ)) ^ (t/η) = Real.exp (-(t*w ξ)) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  simpa only [Pi.neg_apply, he] using h

end Form
end HeatL2

open MeasureTheory ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma inner_translate_integral (a : E) (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, translate a f⟫ = ∫ x, f (x+a) * conj (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translate_coe a f] with x hx
  simp only [RCLike.inner_apply, hx]

omit [FiniteDimensional ℝ F] in
lemma integrable_translate_pair (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) (ν.prod volume) := by
  have hm : StronglyMeasurable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) := by
    exact ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).mul
      (continuous_star.comp_stronglyMeasurable ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro z
    apply (L2.integrable_inner (𝕜 := ℂ) g (translate (A z) f)).congr
    filter_upwards [translate_coe (A z) f] with x hx
    simp only [RCLike.inner_apply, hx]
  · apply Integrable.mono' (integrable_const (‖f‖^2+‖g‖^2)) hm.norm.aestronglyMeasurable.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hfi : Integrable (fun x => ‖f (x+A z)‖^2) volume := (measurePreserving_add_right volume (A z)).integrable_comp_of_integrable
      ((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    have hgi := (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
    calc
      _ ≤ ∫ x, ‖f (x+A z)‖^2+‖g x‖^2 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hfi.add hgi)
        apply Filter.Eventually.of_forall
        intro x
        change ‖f (x+A z)*conj (g x)‖ ≤ ‖f (x+A z)‖^2+‖g x‖^2
        simp only [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖f (x+A z)‖-‖g x‖)]
      _ = _ := by
        rw [integral_add hfi hgi, integral_add_right_eq_self (fun x => ‖f x‖^2) (A z),
          ← norm_sq_integral, ← norm_sq_integral]

lemma inner_average_spatial (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ x, ∫ z, f (x+A z)*conj (g x) ∂ν := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  simp_rw [inner_translate_integral]
  exact integral_integral_swap (integrable_translate_pair A ν f g)

end Spatial
section Density
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma inner_average_density (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average (ContinuousLinearMap.id ℝ E) ν f⟫ =
      ∫ x, ∫ y, (p (y-x) : ℂ) * f y * conj (g x) := by
  rw [inner_average_spatial]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [hν, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpn _), ContinuousLinearMap.id_apply,
    Complex.real_smul, mul_assoc]
  have he (z : E) : (p z : ℂ)*(f (x+z)*conj (g x)) =
      (p ((z+x)-x) : ℂ)*(f (z+x)*conj (g x)) := by simp [add_comm]
  simp_rw [he]
  exact integral_add_right_eq_self (μ := (volume : Measure E))
    (fun y => (p (y-x) : ℂ)*(f y*conj (g x))) x

variable (D : Set E) (hD : MeasurableSet D)

lemma integral_extend_mul (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * (extendLp D hD f) x) = ∫ x in D, a x * f x := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*f y) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma integral_extend_conj (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * conj ((extendLp D hD f) x)) = ∫ x in D, a x * conj (f x) := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*conj (f y)) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma inner_extend (f : Lp ℂ 2 (volume.restrict D)) (g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, extendLp D hD f⟫ = ⟪restrictLp D g, f⟫ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in D, conj (g x)*f x := by
      simpa only [RCLike.inner_apply, mul_comm] using integral_extend_mul D hD f (fun x => conj (g x))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restrictLp_coe D g] with x hx
      simp only [RCLike.inner_apply, hx, mul_comm]

lemma densityKernel_inner (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f g : Lp ℂ 2 (volume.restrict D)) :
    ⟪extendLp D hD g, average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)⟫ =
      ⟪g, kernelOp (densityKernel p hp hpn hpb) f⟫ := by
  rw [inner_average_density ν p hp hpn hν, inner_kernel]
  simp only [densityKernel]
  calc
    _ = ∫ x, (∫ y in D, (p (y-x) : ℂ)*f y)*conj ((extendLp D hD g) x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [integral_mul_const, integral_extend_mul D hD f]
    _ = ∫ x in D, (∫ y in D, (p (y-x) : ℂ)*f y)*conj (g x) :=
      integral_extend_conj D hD g _
    _ = _ := by simp only [integral_mul_const]

lemma extend_kernel_eq (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f : Lp ℂ 2 (volume.restrict D)) :
    extendLp D hD (kernelOp (densityKernel p hp hpn hpb) f) =
      mask D hD (average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_extend, ← mask_inner, ← extend_restrict,
    densityKernel_inner D hD ν p hp hpn hpb hν]

include hD in
lemma restrictLp_norm_le (f : Lp ℂ 2 (volume : Measure E)) : ‖restrictLp D f‖ ≤ ‖f‖ := by
  rw [← extendLp_norm D hD (restrictLp D f), extend_restrict]
  exact mask_norm_le D hD f

lemma compressedAverage_kernel_norm (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] :
    ‖mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD‖ =
      ‖kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)‖ := by
  let T := mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD
  let K := kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)
  change ‖T‖ = ‖K‖
  have he f : T f = extendLp D hD (K (restrictLp D f)) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν, extend_restrict]
    rfl
  have he' f : extendLp D hD (K f) = T (extendLp D hD f) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν]
    change _ = mask D hD (average _ ν (mask D hD (extendLp D hD f)))
    rw [(mask_eq_self_iff D hD _).mpr (extendLp_supported D hD f)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [he, extendLp_norm]
    exact (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (restrictLp_norm_le D hD f) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [← extendLp_norm D hD (K f), he']
    simpa only [extendLp_norm] using T.le_opNorm (extendLp D hD f)

end Density
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.PathLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian heat kernels and autoregressive path laws. -/

section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal RealInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaleMap_selfAdjoint (v : ι → ℝ≥0) : IsSelfAdjoint (scaleMap v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change y i * (scaleMap v x) i = (scaleMap v y) i * x i
  rw [scaleMap_apply, scaleMap_apply]
  ring

lemma symbol_eq (v : ι → ℝ≥0) : HeatL2.gaussianSymbol (scaleMap v) = symbol v := by
  ext ξ
  rw [HeatL2.gaussianSymbol, (scaleMap_selfAdjoint v).adjoint_eq,
    EuclideanSpace.real_norm_sq_eq]
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul, scaleMap_apply, mul_pow,
    Real.sq_sqrt (v i).coe_nonneg]
  ring

lemma average_diagonal_eq (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.average (scaleMap v) (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [HeatL2.average_apply, HeatL2.average_apply, ← stdGaussian_map_scale v]
  change (∫ z, HeatL2.translate z f ∂(stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v)) = _
  exact integral_map (scaleMap v).measurable.aemeasurable
    (HeatL2.translate_continuous f).aestronglyMeasurable

lemma average_diagonal_heat (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.heat (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v) := by
  rw [average_diagonal_eq, HeatL2.average_gaussian_eq_heat]
  congr 1
  exact symbol_eq v

omit [DecidableEq ι] in
lemma kernel_symmetric (v : ι → ℝ≥0) (x y : EuclideanSpace ℝ ι) :
    (kernel v).value (x,y) = (kernel v).value (y,x) := by
  change density v (y-x) = density v (x-y)
  rw [← neg_sub y x, density_neg]

lemma kernel_norm_eq (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)] :
    ‖HeatL2.kernelOp (μ := volume.restrict D) (kernel v)‖ =
      ‖HeatL2.compressedHeat D hD (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖ := by
  unfold kernel
  rw [← HeatL2.compressedAverage_kernel_norm D hD (diagonalLaw v) (density v)
    (density_continuous v).measurable (density_nonneg v) (density_le_zero v)
    (diagonalLaw_density v hv), average_diagonal_heat]
  rfl

end GaussianKernel

open MeasureTheory ProbabilityTheory Set WithLp
open scoped NNReal ENNReal
namespace GaussianKernel

lemma gaussianPDF_logconcave {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (x y : ℝ) :
    gaussianPDFReal 0 v x ^ (1-t) * gaussianPDFReal 0 v y ^ t ≤
      gaussianPDFReal 0 v ((1-t)*x+t*y) := by
  have hvp : (0:ℝ)<v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : 0 < (Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹ := by positivity
  simp only [gaussianPDFReal, sub_zero]
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le,
    Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
  calc
    _ = (((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^(1-t) *
        ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^t) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [Real.exp_add]; ring
    _ = ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
      have hq : ((1-t)*x+t*y)^2 ≤ (1-t)*x^2+t*y^2 := by
        nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-y))]
      have : -( (1-t)*x^2+t*y^2)/(2*(v:ℝ)) ≤ -(((1-t)*x+t*y)^2)/(2*(v:ℝ)) :=
        div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
      convert this using 1; ring

variable {ι : Type*} [Fintype ι]
lemma density_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (x y : EuclideanSpace ℝ ι) :
    density v x ^ (1-t) * density v y ^ t ≤ density v ((1-t) • x + t • y) := by
  unfold density
  rw [← Real.finsetProd_rpow _ _ (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i)),
    ← Real.finsetProd_rpow _ _ (fun i _ => gaussianPDFReal_nonneg 0 (v i) (y i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _)
      (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _)
  · intro i _
    exact gaussianPDF_logconcave (hv i) ht (x i) (y i)

end GaussianKernel

end

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma integral_pi_fin_cons {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → X) → G} (hf : Integrable f (Measure.pi fun _ => μ)) :
    (∫ p, f p ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ x, ∫ p, f (Fin.cons x p) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0
  have he : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have hi : Integrable (fun z : X × (Fin n → X) => f (e.symm z)) (μ.prod (Measure.pi fun _ => μ)) :=
    hp.integrable_comp_of_integrable hf
  rw [← hp.integral_comp e.symm.measurableEmbedding f]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun p => congrArg f (he (x,p)))

section Chain
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)

lemma tailWeight_measurable (n : ℕ) : Measurable (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n hn =>
    exact (k.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
      (hn.comp (((measurable_pi_apply 0).comp measurable_snd).prodMk
        (Measurable.of_eval fun (i : Fin n) => (measurable_pi_apply i.succ).comp measurable_snd)))

lemma tailWeight_nonneg (n : ℕ) (x : X) (p : Fin n → X) : 0 ≤ tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n hn => exact mul_nonneg (k.nonneg _) (hn _ _)

lemma tailWeight_le (n : ℕ) (x : X) (p : Fin n → X) : tailWeight k n x p ≤ k.bound^n := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n hn =>
    rw [tailWeight, pow_succ']
    exact mul_le_mul (k.le_bound _) (hn _ _) (tailWeight_nonneg k n _ _) k.bound_nonneg

lemma tailWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    Integrable (tailWeight k n x) (Measure.pi fun _ : Fin n => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n))
    ((tailWeight_measurable k n).comp measurable_prodMk_left).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n x p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n x p)]
    exact tailWeight_le k n x p

lemma walk_zero (μ : Measure X) (x : X) : walk k μ 0 x = 1 := by
  simp [walk,tailWeight, Measure.real]

lemma walk_succ {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    walk k μ (n+1) x = ∫ y, k.value (x,y) * walk k μ n y ∂μ := by
  rw [walk, integral_pi_fin_cons μ (tailWeight_integrable k (n+1) x)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [tailWeight, Fin.cons_zero, Fin.cons_succ]
  rw [integral_const_mul]
  rfl

lemma kernel_pow_one_coe {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    ((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => (walk k μ n x : ℂ) := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, walk_zero, Complex.ofReal_one] using oneLp_coe (μ := μ)
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [kernelOp_coe k ((kernelOp k ^ n) oneLp)] with x hx
    rw [hx, kernelFun, walk_succ]
    calc
      _ = ∫ y, ((k.value (x,y) * walk k μ n y : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hn] with y hy
        rw [hy, Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal

lemma chainWeight_measurable (n : ℕ) : Measurable (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Measurable f := by
    exact (measurable_pi_apply 0).prodMk
      (Measurable.of_eval fun (i : Fin n) => measurable_pi_apply i.succ)
  exact (tailWeight_measurable k n).comp hf

lemma chainWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (chainWeight k n) (Measure.pi fun _ : Fin (n+1) => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n)) (chainWeight_measurable k n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n (p 0) (fun i => p i.succ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n _ _)]
    exact tailWeight_le k n _ _

lemma pathMass_pi {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    pathMass (μ := μ) k n = ∫ p, chainWeight k n p ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
  rw [pathMass_eq_integral, integral_pi_fin_cons μ (chainWeight_integrable k n)]
  apply integral_congr_ae
  filter_upwards [kernel_pow_one_coe k n] with x hx
  rw [hx,Complex.ofReal_re]
  simp only [chainWeight,Fin.cons_zero,Fin.cons_succ]
  rfl

end Chain
end HeatL2

open MeasureTheory Set
namespace HeatL2
section ChainContinuity
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (k : BoundedKernel X) (hc : Continuous k.value)
include hc
lemma tailWeight_continuous (n : ℕ) : Continuous (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun z : X × (Fin (n+1) → X) =>
      k.value (z.1,z.2 0) * tailWeight k n (z.2 0) (fun i => z.2 i.succ))
    apply Continuous.mul
    · exact hc.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · exact ih.comp (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_pi (fun (i : Fin n) => (continuous_apply i.succ).comp continuous_snd)))

lemma chainWeight_continuous (n : ℕ) : Continuous (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Continuous f := by fun_prop
  exact (tailWeight_continuous k hc n).comp hf
end ChainContinuity
section ChainPos
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
lemma tailWeight_pos (hp : ∀ z, 0 < k.value z) (n : ℕ) (x : X) (p : Fin n → X) :
    0 < tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hp _) (ih _ _)
end ChainPos
section ChainConcavity
variable {X : Type*} [MeasurableSpace X] [AddCommGroup X] [Module ℝ X]
variable (k : BoundedKernel X) {t : ℝ}
variable (hl : ∀ x y : X × X, k.value x^(1-t) * k.value y^t ≤ k.value ((1-t)•x+t•y))
include hl
lemma tailWeight_logconcave (n : ℕ) (x y : X) (p q : Fin n → X) :
    tailWeight k n x p^(1-t) * tailWeight k n y q^t ≤
      tailWeight k n ((1-t)•x+t•y) ((1-t)•p+t•q) := by
  induction n generalizing x y with
  | zero => simp [tailWeight]
  | succ n ih =>
    simp only [tailWeight, Pi.add_apply, Pi.smul_apply]
    rw [Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _),
      Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _)]
    calc
      _ = (k.value (x,p 0)^(1-t) * k.value (y,q 0)^t) *
          (tailWeight k n (p 0) (fun i => p i.succ)^(1-t) *
            tailWeight k n (q 0) (fun i => q i.succ)^t) := by ring
      _ ≤ _ := mul_le_mul (hl (x,p 0) (y,q 0)) (ih _ _ _ _)
        (mul_nonneg (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)
          (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)) (k.nonneg _)

lemma chainWeight_logconcave (n : ℕ) (p q : Fin (n+1) → X) :
    chainWeight k n p^(1-t) * chainWeight k n q^t ≤ chainWeight k n ((1-t)•p+t•q) :=
  tailWeight_logconcave k hl n (p 0) (q 0) (fun i => p i.succ) (fun i => q i.succ)
end ChainConcavity
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Survival-energy estimates and simultaneous diagonal separation. -/

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section Rate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma energy_smul (w : E → ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy w (c • f) = ‖c‖^2 * energy w f := by
  unfold energy
  rw [fourier_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

lemma supported_smul (D : Set E) {f : Lp ℂ 2 (volume : Measure E)}
    (hf : f ∈ supported D) (c : ℂ) : c • f ∈ supported D := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he hn
  simp only [he, Pi.smul_apply, hx hn, smul_zero]

lemma form_le_norm (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    ‖f‖^2 - energy w f ≤ ‖compressedHeat D hD w hw hn‖ * ‖f‖^2 := by
  have hh := (positive_norm_le_iff _ (compressedHeat_positive D hD w hw hn)
    (norm_nonneg _)).mp le_rfl f
  rwa [compressedHeat_inner, (mask_eq_self_iff D hD f).mpr hf] at hh

lemma normalized_energy_lt (D : Set E) (w : E → ℝ)
    {f : Lp ℂ 2 (volume : Measure E)} (hfD : f ∈ supported D) (hfn : f ≠ 0)
    {C : ℝ} (hf : energy w f < C*‖f‖^2) :
    ∃ g : Lp ℂ 2 (volume : Measure E), g ∈ supported D ∧ ‖g‖=1 ∧ energy w g < C := by
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  have hc : ‖c‖ = ‖f‖⁻¹ := by simp [c]
  have hnz : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hfn
  have hnorm : ‖c • f‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hnz]
  refine ⟨c • f, supported_smul D hfD c, hnorm, ?_⟩
  rw [energy_smul, hc]
  have hp : 0 < (‖f‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hfn))
  calc
    _ < (‖f‖⁻¹)^2 * (C*‖f‖^2) := mul_lt_mul_of_pos_left hf hp
    _ = C*((‖f‖⁻¹)^2*‖f‖^2) := by ring
    _ = C := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hnz), mul_one]

lemma exists_supported_energy_lt (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C) (h : C < ‖compressedHeat D hD w hw hn‖) :
    ∃ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D ∧ ‖f‖ = 1 ∧ energy w f < 1-C := by
  obtain ⟨g,hg⟩ := positive_exists_form_gt _ (compressedHeat_positive D hD w hw hn) hC h
  rw [compressedHeat_inner] at hg
  let f := mask D hD g
  change C * ‖g‖^2 < ‖f‖^2 - energy w f at hg
  have hfg : ‖f‖^2 ≤ ‖g‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (mask_norm_le D hD g)
  have hf : energy w f < (1-C)*‖f‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hfg hC
    nlinarith
  have hfn : f ≠ 0 := by
    intro he
    have := energy_nonneg w hn f
    rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hf
    rw [he] at this
    linarith
  exact normalized_energy_lt D w
    ((mask_eq_self_iff D hD f).mp (mask_idempotent D hD g)) hfn hf

lemma exists_energy_lt_of_exp_le (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {c : ℝ} (h : Real.exp (-c) ≤ ‖compressedHeat D hD w hw hn‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D ∧ ‖f‖ = 1 ∧ energy w f < c+ε := by
  have he : Real.exp (-(c+ε/2)) < ‖compressedHeat D hD w hw hn‖ := by
    apply lt_of_lt_of_le _ h
    apply Real.exp_lt_exp.mpr
    linarith
  obtain ⟨f,hf,hnf,hef⟩ := exists_supported_energy_lt D hD w hw hn
    (Real.exp_pos (-(c+ε/2))).le he
  refine ⟨f,hf,hnf,hef.trans_le ?_⟩
  have hbound := loss_le_self (c+ε/2)
  dsimp [loss] at hbound
  linarith

lemma compressed_norm_le_of_energy (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D →
      ‖f‖=1 → 1 - energy w f ≤ C) :
    ‖compressedHeat D hD w hw hn‖ ≤ C := by
  by_contra! hg
  obtain ⟨f,hf,hfn,hfe⟩ := exists_supported_energy_lt D hD w hw hn hC hg
  linarith [h f hf hfn]

lemma compressed_norm_mono_symbol (D : Set E) (hD : MeasurableSet D)
    (w v : E → ℝ) (hw : AEStronglyMeasurable w volume) (hv : AEStronglyMeasurable v volume)
    (hwn : ∀ x, 0 ≤ w x) (hvn : ∀ x, 0 ≤ v x) (h : ∀ x, w x ≤ v x) :
    ‖compressedHeat D hD v hv hvn‖ ≤ ‖compressedHeat D hD w hw hwn‖ := by
  apply compressed_norm_le_of_energy D hD v hv hvn (norm_nonneg _)
  intro f hf hfn
  have hE : energy w f ≤ energy v f := by
    rw [energy,energy]
    apply integral_mono (integrable_energy w hw hwn f) (integrable_energy v hv hvn f)
    intro x
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (h x))) 1
  have hh := form_le_norm D hD w hw hwn hf
  rw [hfn, one_pow, mul_one] at hh
  linarith

lemma compressed_norm_mono_domain (D F : Set E) (hD : MeasurableSet D) (hF : MeasurableSet F)
    (hDF : D ⊆ F) (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    ‖compressedHeat D hD w hw hn‖ ≤ ‖compressedHeat F hF w hw hn‖ := by
  apply compressed_norm_le_of_energy D hD w hw hn (norm_nonneg _)
  intro f hf hfn
  have hfF : f ∈ supported F := by
    change ∀ᵐ x, x ∉ F → f x = 0
    change ∀ᵐ x, x ∉ D → f x = 0 at hf
    filter_upwards [hf] with x hx hnot
    exact hx (fun hxd => hnot (hDF hxd))
  simpa only [hfn,one_pow,mul_one] using form_le_norm F hF w hw hn hfF

lemma compressed_norm_rpow (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    {t η : ℝ} (hη : 0 < η) (hηt : η ≤ t) :
    ‖compressedHeat D hD (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ))‖ ^ (t/η) ≤
    ‖compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ))‖ := by
  let A := compressedHeat D hD (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
    (fun ξ => mul_nonneg hη.le (hn ξ))
  let B := compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
    (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ))
  have hpow : 0 < t/η := div_pos (hη.trans_le hηt) hη
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg A) (norm_nonneg B) hpow).mp
  apply compressed_norm_le_of_energy D hD _ _ _ (Real.rpow_nonneg (norm_nonneg B) _)
  intro f hf hfn
  have hh := heat_form_rpow w hw hn hη hηt f hfn
  have hb := form_le_norm D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
    (fun ξ => mul_nonneg (hη.le.trans hηt) (hn ξ)) hf
  rw [hfn, one_pow, mul_one] at hb
  simp only [heat_inner, hfn, one_pow] at hh
  have ha : 0 ≤ 1-energy (fun ξ => η*w ξ) f := by
    have := energy_le_norm_sq (fun ξ => η*w ξ) (hw.const_mul η).aestronglyMeasurable
      (fun ξ => mul_nonneg hη.le (hn ξ)) f
    rw [hfn,one_pow] at this
    linarith
  exact (Real.le_rpow_inv_iff_of_pos ha (norm_nonneg B) hpow).mpr (hh.trans hb)

lemma heat_form_pos (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ≠ 0) :
    0 < (⟪f, heat w hw hn f⟫).re := by
  rw [heat_inner_integral]
  have hi : Integrable (fun ξ => Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2) := by
    apply integrable_weight _ (Real.continuous_exp.comp_aestronglyMeasurable hw.neg)
      (C := 1) _ (𝓕 f)
    exact Eventually.of_forall fun ξ => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn ξ))
  have hp ξ : 0 ≤ Real.exp (-w ξ) * ‖(𝓕 f) ξ‖^2 := by positivity
  apply lt_of_le_of_ne (integral_nonneg hp)
  intro he
  have ha := (integral_eq_zero_iff_of_nonneg hp hi).mp he.symm
  have hsq : (fun ξ => ‖(𝓕 f) ξ‖^2) =ᵐ[volume] 0 := by
    filter_upwards [ha] with ξ hξ
    exact (mul_eq_zero.mp hξ).resolve_left (Real.exp_ne_zero _)
  have hz : ‖f‖^2 = 0 := by
    rw [← Lp.norm_fourier_eq f, norm_sq_integral, integral_congr_ae hsq]
    simp only [Pi.zero_apply, integral_zero]
  exact (sq_pos_of_pos (norm_pos_iff.mpr hf)).ne' hz

lemma compressed_norm_pos_of_supported (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) (hfn : f ≠ 0) :
    0 < ‖compressedHeat D hD w hw hn‖ := by
  have hh := form_le_norm D hD w hw hn hf
  have hp := heat_form_pos w hw hn hfn
  rw [heat_inner] at hp
  have : 0 < ‖compressedHeat D hD w hw hn‖ * ‖f‖^2 := hp.trans_le hh
  exact pos_of_mul_pos_left this (sq_nonneg _)

lemma oneLp_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] :
    ‖(oneLp : Lp ℂ 2 μ)‖^2 = (μ univ).toReal := by
  rw [norm_sq_integral]
  calc
    _ = ∫ _ : X, (1:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [oneLp_coe (μ := μ)] with x hx
      simp only [hx, norm_one, one_pow]
    _ = _ := by simp [Measure.real]

lemma compressed_norm_pos (D : Set E) (hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] (hDp : 0 < volume D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    0 < ‖compressedHeat D hD w hw hn‖ := by
  apply compressed_norm_pos_of_supported D hD w hw hn (extendLp_supported D hD oneLp)
  intro hz
  have he := extendLp_norm D hD (oneLp : Lp ℂ 2 (volume.restrict D))
  rw [hz, norm_zero] at he
  have hp : (0:ℝ) < (volume D).toReal :=
    ENNReal.toReal_pos hDp.ne' (by simpa only [Measure.restrict_apply_univ] using (measure_ne_top (volume.restrict D) univ))
  have hs := oneLp_norm_sq (μ := volume.restrict D)
  rw [Measure.restrict_apply_univ, ← he, zero_pow (by decide : 2 ≠ 0)] at hs
  linarith

end Rate
end HeatL2

end

section

open Set Finset

namespace EuclideanSteinitz

lemma functional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have he : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, apply_ite]
  conv_lhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

lemma simultaneous_approx {ι F : Type*} [Fintype ι] [Nonempty F]
    (E : F → ι → ℝ) (c : ℝ)
    (hconv : ∀ f g : F, ∀ t ∈ Icc (0:ℝ) 1, ∃ h : F,
       ∀ i, E h i ≤ t * E f i + (1-t) * E g i)
    (hweighted : ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) → ∀ δ > 0,
       ∃ f : F, ∑ i, q i * E f i < c * ∑ i, q i + δ)
    (ε : ℝ) (hε : 0 < ε) : ∃ f : F, ∀ i, E f i < c + ε := by
  classical
  let A : Set (ι → ℝ) := {u | ∃ f : F, ∀ i, E f i < u i}
  have hA : Convex ℝ A := by
    intro u hu v hv a b ha hb hab
    obtain ⟨f, hf⟩ := hu
    obtain ⟨g, hg⟩ := hv
    obtain ⟨h, hh⟩ := hconv f g a ⟨ha, by linarith⟩
    refine ⟨h, fun i => ?_⟩
    have hstrict : a * E f i + b * E g i < a * u i + b * v i := by
      rcases eq_or_lt_of_le ha with hzero | hap
      · have ha0 : a = 0 := hzero.symm
        simp only [ha0, zero_add] at hab
        simp only [ha0, zero_mul, zero_add, hab, one_mul]
        exact hg i
      · have hf' := mul_lt_mul_of_pos_left (hf i) hap
        have hg' := mul_le_mul_of_nonneg_left (hg i).le hb
        linarith
    change E h i < a * u i + b * v i
    have : 1-a=b := by linarith
    rw [this] at hh
    exact (hh i).trans_lt hstrict
  have hAo : IsOpen A := by
    have he : A = ⋃ f : F, ⋂ i : ι, {u : ι → ℝ | E f i < u i} := by
      ext u
      simp only [A, mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [he]
    apply isOpen_iUnion
    intro f
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (continuous_apply i)
  let x : ι → ℝ := fun _ => c+ε
  by_contra hn
  have hx : x ∉ A := hn
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hA hAo hx
  let q : ι → ℝ := fun i => L (Pi.single i 1)
  have hne : A.Nonempty := by
    obtain ⟨f⟩ := ‹Nonempty F›
    exact ⟨fun i => E f i+1, f, fun _ => by linarith⟩
  obtain ⟨u, hu⟩ := hne
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    have hqi : q i < 0 := lt_of_not_ge hneg
    let r := (L u - L x + 1) / (-q i)
    have hr : 0 ≤ r := by
      apply div_nonneg
      · linarith [hL u hu]
      · exact neg_nonneg.mpr hqi.le
    have huv : u + r • Pi.single i 1 ∈ A := by
      obtain ⟨f, hf⟩ := hu
      refine ⟨f, fun j => (hf j).trans_le ?_⟩
      change u j ≤ u j + r * (Pi.single i (1:ℝ) : ι → ℝ) j
      have hs : 0 ≤ (Pi.single i (1:ℝ) : ι → ℝ) j := by simp only [Pi.single_apply]; split_ifs <;> norm_num
      exact le_add_of_nonneg_right (mul_nonneg hr hs)
    have hxv := hL _ huv
    rw [map_add, map_smul, smul_eq_mul] at hxv
    change L x < L u + r * q i at hxv
    have hri : r * q i = -(L u-L x+1) := by
      dsimp [r]
      field_simp [ne_of_lt hqi]
    linarith
  have hsum : 0 < ∑ i, q i := by
    have hnon := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hq i)
    by_contra hzero
    have hz : ∑ i, q i = 0 := le_antisymm (le_of_not_gt hzero) hnon
    have hqi : ∀ i, q i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hq j)).mp hz i (mem_univ _)
    have hLu : L u = 0 := by rw [functional_eq_sum]; simp only [← show ∀ i, q i = L (Pi.single i 1) from fun _ => rfl, hqi, zero_mul, Finset.sum_const_zero]
    have hLx : L x = 0 := by rw [functional_eq_sum]; simp only [← show ∀ i, q i = L (Pi.single i 1) from fun _ => rfl, hqi, zero_mul, Finset.sum_const_zero]
    linarith [hL u hu]
  obtain ⟨f, hf⟩ := hweighted q hq (ε*(∑ i, q i)/2) (by positivity)
  let v : ι → ℝ := fun i => E f i + ε/2
  have hv : v ∈ A := ⟨f, fun _ => by dsimp [v]; linarith⟩
  have hvx := hL v hv
  have hLx : L x = (c+ε) * ∑ i, q i := by
    rw [functional_eq_sum]
    change (∑ i, q i * (c+ε)) = _
    rw [← Finset.sum_mul, mul_comm]
  have hLv : L v = (∑ i, q i * E f i) + (ε/2) * ∑ i, q i := by
    rw [functional_eq_sum]
    change (∑ i, q i * (E f i+ε/2)) = _
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hLx, hLv] at hvx
  linarith

end EuclideanSteinitz

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma mixture_gaussian_energy_le (A : F →L[ℝ] E) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure E)) :
    energy (gaussianSymbol A) (mixture t ht ht' f g) ≤
      t * energy (gaussianSymbol A) f + (1-t) * energy (gaussianSymbol A) g := by
  simp only [gaussian_energy_difference]
  have hh := integral_mono
    (integrable_difference_sq A (ProbabilityTheory.stdGaussian F) (mixture t ht ht' f g))
    (((integrable_difference_sq A (ProbabilityTheory.stdGaussian F) f).const_mul t).add
      ((integrable_difference_sq A (ProbabilityTheory.stdGaussian F) g).const_mul (1-t)))
    (fun z => mixture_translation_sq_le t ht ht' f g (A z))
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_difference_sq A _ f).const_mul t)
      ((integrable_difference_sq A _ g).const_mul (1-t)), integral_const_mul, integral_const_mul] at hh
  linarith

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mixture_diagonal_energy_le (v : ι → ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (GaussianKernel.symbol v) (mixture t ht ht' f g) ≤
      t * energy (GaussianKernel.symbol v) f + (1-t) * energy (GaussianKernel.symbol v) g := by
  rw [← GaussianKernel.symbol_eq]
  exact mixture_gaussian_energy_le _ t ht ht' f g

end
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
namespace Diagonal
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma coordSymbol_nonneg (i : ι) (ξ : EuclideanSpace ℝ ι) : 0 ≤ coordSymbol i ξ := sq_nonneg _
omit [Fintype ι] in
lemma coordSymbol_continuous (i : ι) : Continuous (coordSymbol i) := by
  unfold coordSymbol
  fun_prop

lemma symbol_single [DecidableEq ι] (i : ι) (η : ℝ≥0) :
    GaussianKernel.symbol (Pi.single i (2*η)) = fun ξ => (η:ℝ)*coordSymbol i ξ := by
  ext ξ
  simp only [GaussianKernel.symbol, coordSymbol, Pi.single_apply, apply_ite,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma exists_unit_of_bound {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c : ℝ}
    (h : Bound D hD c) :
    ∃ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)), f ∈ supported D ∧ ‖f‖ = 1 := by
  have hb := h 0
  simp only [Pi.zero_apply, NNReal.coe_zero, Finset.sum_const_zero, mul_zero] at hb
  obtain ⟨f,hf,hn,_⟩ := exists_energy_lt_of_exp_le D hD _
    (GaussianKernel.symbol_continuous 0).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg 0) (c := 0) (by simpa only [neg_zero] using hb) (ε := 1) (by norm_num)
  exact ⟨f,hf,hn⟩

lemma symbol_mean (η : ℝ) (hη : 0 ≤ η) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    GaussianKernel.symbol (fun i => ⟨2*η*q i, mul_nonneg (mul_nonneg (by norm_num) hη) (hq i)⟩) =
      fun ξ => ∑ i, q i * (η*coordSymbol i ξ) := by
  ext ξ
  unfold GaussianKernel.symbol coordSymbol
  change (∑ i, (2*η*q i)*(2*Real.pi*ξ i)^2)/2 = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma coord_mixture_energy_le [DecidableEq ι] (i : ι) (η : ℝ) (hη : 0 ≤ η)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (f g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (fun ξ => η*coordSymbol i ξ) (mixture t ht.1 ht.2 f g) ≤
      t*energy (fun ξ => η*coordSymbol i ξ) f +
        (1-t)*energy (fun ξ => η*coordSymbol i ξ) g := by
  let ηn : ℝ≥0 := ⟨η,hη⟩
  have hh := mixture_diagonal_energy_le (Pi.single i (2*ηn)) t ht.1 ht.2 f g
  rw [symbol_single i ηn] at hh
  exact hh

lemma simultaneous_coordinate_energy {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D}
    {c : ℝ} (hB : Bound D hD c) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      f ∈ supported D ∧ ‖f‖ = 1 ∧ ∀ i, energy (fun ξ => η*coordSymbol i ξ) f < η*(c+ε) := by
  classical
  let F := {f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) | f ∈ supported D ∧ ‖f‖ = 1}
  obtain ⟨f₀,hf₀,hn₀⟩ := exists_unit_of_bound hB
  let fzero : F := ⟨f₀,hf₀,hn₀⟩
  let : Nonempty F := ⟨fzero⟩
  let E : F → ι → ℝ := fun f i => energy (fun ξ => η*coordSymbol i ξ) f.val
  have hconv : ∀ f g : F, ∀ t ∈ Icc (0:ℝ) 1, ∃ h : F,
      ∀ i, E h i ≤ t*E f i+(1-t)*E g i := by
    intro f g t ht
    let m := mixture t ht.1 ht.2 f.val g.val
    have hm : ‖m‖=1 := by
      have hh := mixture_norm_sq t ht.1 ht.2 f.val g.val
      rw [f.property.2,g.property.2,one_pow] at hh
      change ‖m‖^2 = _ at hh
      nlinarith [norm_nonneg m]
    refine ⟨⟨m,mixture_supported D t ht.1 ht.2 f.val g.val f.property.1 g.property.1,hm⟩,?_⟩
    intro i
    exact coord_mixture_energy_le i η hη.le t ht f.val g.val
  have hweighted : ∀ q : ι → ℝ, (∀ i,0 ≤ q i) → ∀ δ > 0,
      ∃ f : F, ∑ i, q i*E f i < (η*c)*∑ i,q i+δ := by
    intro q hq δ hδ
    let S := ∑ i,q i
    have hSn : 0 ≤ S := Finset.sum_nonneg (fun i _ => hq i)
    by_cases hS : S=0
    · have hq0 : ∀ i,q i=0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hq j)).mp hS i (Finset.mem_univ i)
      refine ⟨fzero,?_⟩
      simpa only [hq0,zero_mul,Finset.sum_const_zero,mul_zero,zero_add] using hδ
    have hSp : 0 < S := lt_of_le_of_ne hSn (Ne.symm hS)
    let p : ι → ℝ := fun i => q i/S
    have hp : ∀ i,0 ≤ p i := fun i => div_nonneg (hq i) hSn
    have hpsum : ∑ i,p i=1 := by
      dsimp [p]
      rw [← Finset.sum_div]
      exact div_self hS
    let v : ι → ℝ≥0 := fun i => ⟨2*η*p i,mul_nonneg (mul_nonneg (by norm_num) hη.le) (hp i)⟩
    have hvsum : ∑ i,(v i:ℝ)=2*η := by
      change (∑ i,(2*η)*p i)=2*η
      rw [← Finset.mul_sum,hpsum,mul_one]
    have hv := hB v
    rw [hvsum] at hv
    have he : -(c/2)*(2*η)=-(η*c) := by ring
    rw [he] at hv
    obtain ⟨f,hf,hn,henergy⟩ := exists_energy_lt_of_exp_le D hD (GaussianKernel.symbol v)
      (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)
      hv (div_pos hδ hSp)
    have hmean := energy_mean_ge Finset.univ p (fun i ξ => η*coordSymbol i ξ)
      (fun i _ => hp i) hpsum
      (fun i _ => ((coordSymbol_continuous i).const_mul η).aestronglyMeasurable)
      (fun i _ ξ => mul_nonneg hη.le (coordSymbol_nonneg i ξ)) f
    have hve : GaussianKernel.symbol v = fun ξ => ∑ i,p i*(η*coordSymbol i ξ) :=
      symbol_mean η hη.le p hp
    rw [← hve] at hmean
    have hsum : ∑ i,q i*energy (fun ξ => η*coordSymbol i ξ) f =
        S*(∑ i,p i*energy (fun ξ => η*coordSymbol i ξ) f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [p]
      field_simp
    refine ⟨⟨f,hf,hn⟩,?_⟩
    change (∑ i,q i*energy (fun ξ => η*coordSymbol i ξ) f) < (η*c)*S+δ
    rw [hsum]
    have hh := mul_lt_mul_of_pos_left (hmean.trans_lt henergy) hSp
    have hcancel : S*(η*c+δ/S)=(η*c)*S+δ := by field_simp
    exact hh.trans_eq hcancel
  obtain ⟨f,hf⟩ := EuclideanSteinitz.simultaneous_approx E (η*c) hconv hweighted (η*ε)
    (mul_pos hη hε)
  refine ⟨f.val,f.property.1,f.property.2,fun i => ?_⟩
  simpa only [mul_add] using hf i

end Diagonal
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Prekopa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prékopa inequalities and Gaussian log-concavity. -/

section

open MeasureTheory Set Filter
open scoped Topology

namespace Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma gauss_prod {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    gauss c x = ∏ i, Real.exp (-c * (x i)^2) := by
  rw [gauss, ← Real.exp_sum, Finset.mul_sum]

lemma gauss_pos {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : 0 < gauss c x :=
  Real.exp_pos _

lemma gauss_le_one {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) : gauss c x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma gauss_integrable {n : ℕ} {c : ℝ} (hc : 0 < c) : Integrable (@gauss n c) := by
  simp only [funext (gauss_prod c), volume_pi]
  exact Integrable.fin_nat_prod (fun _ => integrable_exp_neg_mul_sq hc)

/-- The Prékopa–Leindler inequality on `Fin n → ℝ` for continuous, positive functions with a
Gaussian upper bound (OpenAI's `Nice`, written out), derived from the published
`ConvexOptimization.prekopa_leindler` (measurable functions to `ℝ≥0∞` on `EuclideanSpace`). -/
lemma fin {n : ℕ} {f g h : (Fin n → ℝ) → ℝ} {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x) (hhpos : ∀ x, 0 < h x)
    (hfb : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, f x ≤ C * Real.exp (-c * ∑ i, (x i)^2))
    (hgb : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, g x ≤ C * Real.exp (-c * ∑ i, (x i)^2))
    (hhb : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, h x ≤ C * Real.exp (-c * ∑ i, (x i)^2))
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α) • x + α • y)) :
    (∫ x, f x) ^ (1-α) * (∫ x, g x) ^ α ≤ ∫ x, h x := by
  have hG : ∀ {c : ℝ}, 0 < c →
      Integrable (fun x : Fin n → ℝ => Real.exp (-c * ∑ i, (x i)^2)) := by
    intro c hc
    have he : (fun x : Fin n → ℝ => Real.exp (-c * ∑ i, (x i)^2)) =
        fun x => ∏ i, Real.exp (-c * (x i)^2) := by
      funext x; rw [← Real.exp_sum, Finset.mul_sum]
    rw [he, volume_pi]
    exact Integrable.fin_nat_prod (fun _ => integrable_exp_neg_mul_sq hc)
  have hint : ∀ {φ : (Fin n → ℝ) → ℝ}, Continuous φ → (∀ x, 0 < φ x) →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, φ x ≤ C * Real.exp (-c * ∑ i, (x i)^2)) →
      Integrable φ := by
    intro φ hφc hφp ⟨C, c, _, hc, hb⟩
    apply ((hG hc).const_mul C).mono' hφc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (hφp x)]
    exact hb x
  have hfi := hint hfc hfpos hfb
  have hgi := hint hgc hgpos hgb
  have hhi := hint hhc hhpos hhb
  rcases eq_or_lt_of_le hα.1 with h0 | h0
  · subst h0
    simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact integral_mono hfi hhi fun x => by simpa using hfg x x
  rcases eq_or_lt_of_le hα.2 with h1 | h1
  · subst h1
    simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
    exact integral_mono hgi hhi fun x => by simpa using hfg x x
  let e : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) := WithLp.ofLp
  have hep : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin n)
  have hlin : ∀ x y : EuclideanSpace ℝ (Fin n), e ((1-α) • x + α • y) = (1-α) • e x + α • e y :=
    fun x y => by simp [e]
  have hl : ∀ {φ : (Fin n → ℝ) → ℝ}, Continuous φ → (∀ x, 0 < φ x) → Integrable φ →
      ∫⁻ x, ENNReal.ofReal (φ (e x)) = ENNReal.ofReal (∫ x, φ x) := by
    intro φ hφc hφp hφi
    refine (hep.lintegral_comp (f := ENNReal.ofReal ∘ φ)
      (ENNReal.measurable_ofReal.comp hφc.measurable)).trans ?_
    exact (ofReal_integral_eq_lintegral_ofReal hφi (ae_of_all _ fun x => (hφp x).le)).symm
  have hpl := ConvexOptimization.prekopa_leindler α h0 h1
    (fun x => ENNReal.ofReal (f (e x))) (fun x => ENNReal.ofReal (g (e x)))
    (fun x => ENNReal.ofReal (h (e x)))
    (ENNReal.measurable_ofReal.comp (hfc.measurable.comp hep.measurable))
    (ENNReal.measurable_ofReal.comp (hgc.measurable.comp hep.measurable))
    (ENNReal.measurable_ofReal.comp (hhc.measurable.comp hep.measurable))
    (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hfpos _).le (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (hgpos _).le h0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hfpos _).le _), hlin]
      exact ENNReal.ofReal_le_ofReal (hfg _ _))
  rw [hl hfc hfpos hfi, hl hgc hgpos hgi, hl hhc hhpos hhi,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (hfpos x).le) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (hgpos x).le) h0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg fun x => (hfpos x).le) _)] at hpl
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => (hhpos x).le)).mp hpl

lemma fin_of_nice {n : ℕ} {f g h : (Fin n → ℝ) → ℝ} {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hf : Nice f) (hg : Nice g) (hh : Nice h)
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α) • x + α • y)) :
    (∫ x, f x) ^ (1-α) * (∫ x, g x) ^ α ≤ ∫ x, h x :=
  fin hα hf.continuous hg.continuous hh.continuous hf.positive hg.positive hh.positive
    hf.bound hg.bound hh.bound hfg

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter Metric
open scoped Topology

lemma infDist_combination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {A B C : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) (x y : E) :
    infDist ((1-α) • x + α • y) C ≤ (1-α)*infDist x A + α*infDist y B := by
  obtain ⟨a, ha, hea⟩ := hA.exists_infDist_eq_dist hnA x
  obtain ⟨b, hb, heb⟩ := hB.exists_infDist_eq_dist hnB y
  rw [hea, heb]
  apply (infDist_le_dist_of_mem (hABC a ha b hb)).trans
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have he : (1-α) • x + α • y - ((1-α) • a + α • b) =
      (1-α) • (x-a) + α • (y-b) := by module
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hα.2), abs_of_nonneg hα.1]

lemma sum_sq_combination {n : ℕ} {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (x y : Fin n → ℝ) :
    (∑ i, (((1-α) • x + α • y) i)^2) ≤ (1-α)*(∑ i, (x i)^2) + α*(∑ i, (y i)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he := mul_nonneg (mul_nonneg hα.1 (sub_nonneg.mpr hα.2)) (sq_nonneg (x i - y i))
  nlinarith

lemma approx_nice {n : ℕ} {c : ℝ} (hc : 0 < c) (k : ℕ) (A : Set (Fin n → ℝ)) :
    Nice (approx c k A) := by
  constructor
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _
      (fun i _ => (continuous_apply i).pow 2)))).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_infDist_pt A)))
  · intro x
    exact mul_pos (gauss_pos _ _) (Real.exp_pos _)
  · refine ⟨1, c, zero_lt_one, hc, ?_⟩
    intro x
    dsimp [approx]
    rw [one_mul]
    exact mul_le_of_le_one_right (gauss_pos _ _).le
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))

lemma approx_interpolate {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hnA : A.Nonempty) (hnB : B.Nonempty)
    {α c : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) (k : ℕ) (x y : Fin n → ℝ) :
    approx c k A x ^ (1-α) * approx c k B y ^ α ≤ approx c k C ((1-α) • x + α • y) := by
  simp only [approx, gauss, ← Real.exp_add, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left (sum_sq_combination hα x y) hc
  have h2 := mul_le_mul_of_nonneg_left (infDist_combination hA hB hnA hnB hα hABC x y)
    (show (0 : ℝ) ≤ (k : ℝ) by positivity)
  nlinarith

lemma approx_tendsto {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsClosed A)
    (hnA : A.Nonempty) (c : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun k => approx c k A x) atTop (𝓝 (A.indicator (gauss c) x)) := by
  by_cases hx : x ∈ A
  · simp [approx, infDist_zero_of_mem hx, hx]
  · rw [indicator_of_notMem hx]
    have hd := (hA.notMem_iff_infDist_pos hnA).mp hx
    have he : Tendsto (fun k : ℕ => -(k : ℝ) * infDist x A) atTop atBot := by
      have ht : Tendsto (fun k : ℕ => (k : ℝ) * infDist x A) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hd
      have hn : Tendsto (fun k : ℕ => -((k : ℝ) * infDist x A)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ht
      convert hn using 1; simp only [neg_mul]
    simpa only [mul_zero, approx, Function.comp_apply] using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp he)

end Prekopa

open MeasureTheory Set ProbabilityTheory
namespace Prekopa

lemma convex_closure_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hA : Convex ℝ A) : closure A =ᵐ[μ] A := by
  have hn : ∀ᵐ x ∂μ, x ∉ frontier A := by
    rw [ae_iff]
    simpa using hA.addHaar_frontier μ
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · intro hc
    by_contra ha
    exact hx ⟨hc, fun hi => ha (interior_subset hi)⟩
  · exact fun hx => subset_closure hx

lemma combination_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C : Set E} {α : ℝ}
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ∀ a ∈ closure A, ∀ b ∈ closure B, (1-α) • a + α • b ∈ closure C := by
  have hm : MapsTo (fun p : E × E => (1-α) • p.1 + α • p.2) (A ×ˢ B) C :=
    fun p hp => hABC p.1 hp.1 p.2 hp.2
  have hc := hm.closure_of_continuousOn (by fun_prop)
  intro a ha b hb
  exact hc (x := (a,b)) (by simpa only [closure_prod_eq, mem_prod] using And.intro ha hb)

end Prekopa
open MeasureTheory Set ProbabilityTheory

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace Prekopa
variable {n : ℕ}
lemma weighted_approx_nice {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {c : ℝ} (hc : 0 < c) (k : ℕ) (A : Set (Fin n → ℝ)) :
    Nice (fun x => w x * approx c k A x) := by
  constructor
  · exact hw.mul (approx_nice hc k A).continuous
  · intro x; exact mul_pos (hp x) ((approx_nice hc k A).positive x)
  · refine ⟨M,c,hM,hc,?_⟩
    intro x
    have ha : approx c k A x ≤ gauss c x := by
      unfold approx
      exact mul_le_of_le_one_right (gauss_pos _ _).le
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))
    exact mul_le_mul (hb x) ha ((approx_nice hc k A).positive x).le hM.le

lemma integral_weighted_approx_tendsto {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A : Set (Fin n → ℝ)} (hA : IsClosed A)
    (hnA : A.Nonempty) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => ∫ x, w x * approx c k A x) atTop
      (𝓝 (∫ x in A, w x * gauss c x)) := by
  rw [← integral_indicator hA.measurableSet]
  apply tendsto_integral_of_dominated_convergence (fun x => M * gauss c x)
    (fun k => (weighted_approx_nice hw hp hM hb hc k A).continuous.aestronglyMeasurable)
    ((gauss_integrable hc).const_mul M)
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos ((weighted_approx_nice hw hp hM hb hc k A).positive x)]
    apply mul_le_mul (hb x) _ ((approx_nice hc k A).positive x).le hM.le
    unfold approx
    exact mul_le_of_le_one_right (gauss_pos _ _).le
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))
  · filter_upwards [] with x
    convert (tendsto_const_nhds.mul (approx_tendsto hA hnA c x)) using 1
    by_cases hx : x ∈ A <;> simp [hx]

lemma weighted_gauss_closed {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α c : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hc : 0 < c)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x * gauss c x) ^ (1-α) *
      (∫ x in B, w x * gauss c x) ^ α ≤ ∫ x in C, w x * gauss c x := by
  have hnC : C.Nonempty := by
    obtain ⟨a,ha⟩ := hnA
    obtain ⟨b,hb'⟩ := hnB
    exact ⟨_,hABC a ha b hb'⟩
  apply le_of_tendsto_of_tendsto
    (((integral_weighted_approx_tendsto hw hp hM hb hA hnA hc).rpow_const
      (Or.inr (sub_nonneg.mpr hα.2))).mul
      ((integral_weighted_approx_tendsto hw hp hM hb hB hnB hc).rpow_const (Or.inr hα.1)))
    (integral_weighted_approx_tendsto hw hp hM hb hC hnC hc)
  apply Filter.Eventually.of_forall
  intro k
  apply fin_of_nice hα (weighted_approx_nice hw hp hM hb hc k A)
    (weighted_approx_nice hw hp hM hb hc k B) (weighted_approx_nice hw hp hM hb hc k C)
  intro x y
  rw [Real.mul_rpow (hp x).le ((approx_nice hc k A).positive x).le,
    Real.mul_rpow (hp y).le ((approx_nice hc k B).positive y).le]
  calc
    _ = (w x ^ (1-α) * w y ^ α) * (approx c k A x ^ (1-α) * approx c k B y ^ α) := by ring
    _ ≤ w ((1-α) • x + α • y) * approx c k C ((1-α) • x + α • y) :=
      mul_le_mul (hl x y) (approx_interpolate hA hB hnA hnB hα hc.le hABC k x y)
        (mul_nonneg (Real.rpow_nonneg ((approx_nice hc k A).positive x).le _)
          (Real.rpow_nonneg ((approx_nice hc k B).positive y).le _)) (hp _).le

lemma integral_weighted_gauss_tendsto {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (_hM : 0 < M)
    (hb : ∀ x, w x ≤ M) (A : Set (Fin n → ℝ)) [IsFiniteMeasure (volume.restrict A)] :
    Tendsto (fun k : ℕ => ∫ x in A, w x * gauss (1/((k:ℝ)+1)) x) atTop
      (𝓝 (∫ x in A, w x)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun k => hw.aestronglyMeasurable.mul
      ((Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)))).aestronglyMeasurable))
    (integrable_const M)
  · intro k
    filter_upwards [] with x
    change ‖w x * gauss (1/((k:ℝ)+1)) x‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hp x) (gauss_pos _ _))]
    exact (mul_le_of_le_one_right (hp x).le (gauss_le_one (by positivity) x)).trans (hb x)
  · filter_upwards [] with x
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.mul_const (∑ i, (x i)^2)
    have he := Real.continuous_exp.continuousAt.tendsto.comp ht
    simpa [gauss] using tendsto_const_nhds.mul he

lemma bounded_weight_closed {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    [IsFiniteMeasure (volume.restrict A)] [IsFiniteMeasure (volume.restrict B)]
    [IsFiniteMeasure (volume.restrict C)]
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x) ^ (1-α) * (∫ x in B, w x) ^ α ≤ ∫ x in C, w x := by
  apply le_of_tendsto_of_tendsto
    (((integral_weighted_gauss_tendsto hw hp hM hb A).rpow_const
      (Or.inr (sub_nonneg.mpr hα.2))).mul
      ((integral_weighted_gauss_tendsto hw hp hM hb B).rpow_const (Or.inr hα.1)))
    (integral_weighted_gauss_tendsto hw hp hM hb C)
  exact Filter.Eventually.of_forall fun k =>
    weighted_gauss_closed hw hp hM hb hA hB hC hnA hnB hα (by positivity) hl hABC

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma bounded_weight_compact_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {w : E → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set E}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x ∂μ) ^ (1-α) * (∫ x in B, w x ∂μ) ^ α ≤ ∫ x in C, w x ∂μ := by
  let e := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure E := volume.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν μ
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have heμ : volume.map e = (c : ℝ≥0∞) • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpre (D : Set E) (hD : IsCompact D) : IsCompact (e ⁻¹' D) := by
    exact e.toHomeomorph.isCompact_preimage.mpr hD
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' A)) := ⟨by simpa using (hpre A hA).measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' B)) := ⟨by simpa using (hpre B hB).measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' C)) := ⟨by simpa using (hpre C hC).measure_lt_top⟩
  have hi (D : Set E) (hD : IsCompact D) :
      (∫ x in e ⁻¹' D, w (e x)) = (c:ℝ) * ∫ x in D, w x ∂μ := by
    rw [← setIntegral_map hD.isClosed.measurableSet hw.aestronglyMeasurable
      e.continuous.measurable.aemeasurable, heμ, Measure.restrict_smul, integral_smul_measure]
    simp

  have hl' : ∀ x y, w (e x) ^ (1-α) * w (e y) ^ α ≤ w (e ((1-α) • x + α • y)) := by
    intro x y
    simpa only [map_add,map_smul] using hl (e x) (e y)
  have hcomb : ∀ a ∈ e ⁻¹' A, ∀ b ∈ e ⁻¹' B, (1-α) • a + α • b ∈ e ⁻¹' C := by
    intro a ha b hb'
    change e ((1-α) • a + α • b) ∈ C
    simpa only [map_add,map_smul] using hABC (e a) ha (e b) hb'
  have hnA' : (e ⁻¹' A).Nonempty := hnA.preimage e.surjective
  have hnB' : (e ⁻¹' B).Nonempty := hnB.preimage e.surjective
  have hh := bounded_weight_closed (hw.comp e.continuous) (fun x => hp (e x)) hM
    (fun x => hb (e x)) (hpre A hA).isClosed (hpre B hB).isClosed (hpre C hC).isClosed
    hnA' hnB' hα hl' hcomb
  simp only [Function.comp_apply] at hh
  rw [hi A hA, hi B hB, hi C hC,
    Real.mul_rpow (by positivity) (integral_nonneg (fun x => (hp x).le)),
    Real.mul_rpow (by positivity) (integral_nonneg (fun x => (hp x).le))] at hh
  have hcp : (0:ℝ)<c := hc
  have hcPow : (c:ℝ)^(1-α) * (c:ℝ)^α = (c:ℝ) := by
    rw [← Real.rpow_add hcp, sub_add_cancel, Real.rpow_one]
  have heq : (c:ℝ)^(1-α) * (∫ x in A, w x ∂μ)^(1-α) *
      ((c:ℝ)^α * (∫ x in B, w x ∂μ)^α) =
      (c:ℝ) * ((∫ x in A, w x ∂μ)^(1-α) * (∫ x in B, w x ∂μ)^α) := by
    calc
      _ = ((c:ℝ)^(1-α) * (c:ℝ)^α) *
          ((∫ x in A, w x ∂μ)^(1-α) * (∫ x in B, w x ∂μ)^α) := by ring
      _ = _ := by rw [hcPow]
  rw [heq] at hh
  exact (mul_le_mul_iff_right₀ hcp).mp hh

lemma bounded_weight_convex_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {w : E → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set E}
    (ha : Bornology.IsBounded A) (hb' : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hcC : Convex ℝ C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x ∂μ) ^ (1-α) * (∫ x in B, w x ∂μ) ^ α ≤ ∫ x in C, w x ∂μ := by
  have hh := bounded_weight_compact_haar μ hw hp hM hb ha.isCompact_closure
    hb'.isCompact_closure hc.isCompact_closure hnA.closure hnB.closure hα hl
    (combination_closure hABC)
  rwa [setIntegral_congr_set (convex_closure_ae μ hcA),
    setIntegral_congr_set (convex_closure_ae μ hcB),
    setIntegral_congr_set (convex_closure_ae μ hcC)] at hh

end Prekopa

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.KernelConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity and norm inequalities for Gaussian kernels. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma le_of_shifted_pow_le_const_mul_pow {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^(n+2) ≤ K*b^n) : a ≤ b := by
  by_cases hz : a = 0
  · simpa [hz] using hb
  have hp : 0 < a^2 := sq_pos_of_ne_zero hz
  apply le_of_pow_le_const_mul_pow ha hb (C := K/a^2)
  intro n
  rw [div_mul_eq_mul_div, le_div_iff₀ hp, ← pow_add]
  exact h n

section
variable {X : Type*} [MeasurableSpace X]
variable (k : BoundedKernel X) (hs : ∀ x y, k.value (x,y) = k.value (y,x))
variable (μ ν ω : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ω]

include hs in
lemma kernel_norm_logconcave_of_pathMass {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (h : ∀ n, pathMass (μ := μ) k n^(1-t) * pathMass (μ := ν) k n^t ≤ pathMass (μ := ω) k n) :
    ‖kernelOp (μ := μ) k‖^(1-t) * ‖kernelOp (μ := ν) k‖^t ≤ ‖kernelOp (μ := ω) k‖ := by
  let A := k.bound^2 * ‖(oneLp : Lp ℂ 2 μ)‖^2
  let B := k.bound^2 * ‖(oneLp : Lp ℂ 2 ν)‖^2
  let C := ‖(oneLp : Lp ℂ 2 ω)‖^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply le_of_shifted_pow_le_const_mul_pow (by positivity) (norm_nonneg _)
    (K := A^(1-t)*B^t*C)
  intro n
  rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _), Real.rpow_pow_comm (norm_nonneg _)]
  calc
    _ ≤ (A*pathMass (μ := μ) k n)^(1-t) * (B*pathMass (μ := ν) k n)^t := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) (sub_nonneg.mpr ht.2)
      · exact Real.rpow_le_rpow (by positivity) (kernel_norm_pow_le_pathMass k hs n) ht.1
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (mul_nonneg hA (pathMass_nonneg k n)) _
    _ = (A^(1-t)*B^t) * (pathMass (μ := μ) k n^(1-t)*pathMass (μ := ν) k n^t) := by
      rw [Real.mul_rpow hA (pathMass_nonneg k n), Real.mul_rpow hB (pathMass_nonneg k n)]
      ring
    _ ≤ (A^(1-t)*B^t)*pathMass (μ := ω) k n :=
      mul_le_mul_of_nonneg_left (h n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ ≤ (A^(1-t)*B^t)*(C*‖kernelOp (μ := ω) k‖^n) :=
      mul_le_mul_of_nonneg_left (pathMass_le k n) (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
    _ = _ := by ring
end

section Haar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddHaarMeasure]
variable (k : BoundedKernel E) (hk : Continuous k.value) (hp : ∀ z, 0 < k.value z)
variable {A B C : Set E} [IsFiniteMeasure (volume.restrict A)]
  [IsFiniteMeasure (volume.restrict B)] [IsFiniteMeasure (volume.restrict C)]

include hk hp in
lemma pathMass_logconcave_haar
    (ha : Bornology.IsBounded A) (hb : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hca : Convex ℝ A) (hcb : Convex ℝ B) (hcc : Convex ℝ C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hl : ∀ x y : E × E, k.value x^(1-t)*k.value y^t ≤ k.value ((1-t)•x+t•y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-t)•a+t•b ∈ C) (n : ℕ) :
    pathMass (μ := volume.restrict A) k n^(1-t) * pathMass (μ := volume.restrict B) k n^t ≤
      pathMass (μ := volume.restrict C) k n := by
  let PA := Set.pi univ (fun _ : Fin (n+1) => A)
  let PB := Set.pi univ (fun _ : Fin (n+1) => B)
  let PC := Set.pi univ (fun _ : Fin (n+1) => C)
  have hnePA : PA.Nonempty := by
    obtain ⟨a,ha'⟩ := hneA
    exact ⟨fun _ => a, fun _ _ => ha'⟩
  have hnePB : PB.Nonempty := by
    obtain ⟨b,hb'⟩ := hneB
    exact ⟨fun _ => b, fun _ _ => hb'⟩
  have hM : 0 < k.bound^n := by
    have : 0 < k.bound := (hp (0,0)).trans_le (k.le_bound _)
    positivity
  have hwpos (p : Fin (n+1) → E) : 0 < chainWeight k n p := tailWeight_pos k hp n _ _
  have hh := Prekopa.bounded_weight_convex_haar (volume : Measure (Fin (n+1) → E))
    (chainWeight_continuous k hk n) hwpos hM (fun p => tailWeight_le k n (p 0) (fun i => p i.succ))
    (Bornology.IsBounded.pi (fun _ => ha)) (Bornology.IsBounded.pi (fun _ => hb))
    (Bornology.IsBounded.pi (fun _ => hc))
    (convex_pi (fun _ _ => hca)) (convex_pi (fun _ _ => hcb)) (convex_pi (fun _ _ => hcc))
    hnePA hnePB ht (chainWeight_logconcave k hl n) (by
      intro a ha' b hb' i hi
      exact hABC (a i) (ha' i hi) (b i) (hb' i hi))
  simpa only [pathMass_pi, volume_pi, Measure.restrict_pi_pi] using hh

end Haar
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma kernel_value_continuous (v : ι → ℝ≥0) : Continuous (kernel v).value := by
  exact (density_continuous v).comp (continuous_snd.sub continuous_fst)

lemma kernel_value_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : 0 < (kernel v).value z :=
  density_pos v hv _

lemma kernel_value_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (kernel v).value x^(1-t)*(kernel v).value y^t ≤ (kernel v).value ((1-t)•x+t•y) := by
  change density v (x.2-x.1)^(1-t)*density v (y.2-y.1)^t ≤
    density v (((1-t)•x+t•y).2-((1-t)•x+t•y).1)
  have he : ((1-t)•x+t•y).2-((1-t)•x+t•y).1 =
      (1-t)•(x.2-x.1)+t•(y.2-y.1) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    module
  rw [he]
  exact density_logconcave v hv ht (x.2-x.1) (y.2-y.1)

lemma compressed_norm_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {A B C : Set (EuclideanSpace ℝ ι)} (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C)
    (ha : Bornology.IsBounded A) (hb : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hca : Convex ℝ A) (hcb : Convex ℝ B) (hcc : Convex ℝ C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-t)•a+t•b ∈ C) :
    ‖HeatL2.compressedHeat A hAo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖^(1-t) *
    ‖HeatL2.compressedHeat B hBo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖^t ≤
    ‖HeatL2.compressedHeat C hCo.measurableSet (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖ := by
  classical
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr ha.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  rw [← kernel_norm_eq v hv A hAo.measurableSet, ← kernel_norm_eq v hv B hBo.measurableSet,
    ← kernel_norm_eq v hv C hCo.measurableSet]
  apply HeatL2.kernel_norm_logconcave_of_pathMass (kernel v) (kernel_symmetric v) _ _ _ ht
  intro n
  exact HeatL2.pathMass_logconcave_haar (kernel v) (kernel_value_continuous v) (kernel_value_pos v hv)
    ha hb hc hca hcb hcc hneA hneB ht (kernel_value_logconcave v hv ht) hABC n

end GaussianKernel

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Rearrangement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Steiner rearrangement and shifted section geometry. -/

section

open Set MeasureTheory
open scoped Pointwise
namespace ShiftedSections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma section_mix {K : Set E} (hK : Convex ℝ K) (e : E) (ell : ℝ)
    {y z : E} {s r a b : ℝ} (hy : y ∈ sectionDomain K e ell s)
    (hz : z ∈ sectionDomain K e ell r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • y+b • z ∈ sectionDomain K e ell (a*s+b*r) := by
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  obtain ⟨d,hd,hdl,hdr⟩ := hz
  refine ⟨a*c+b*d, ?_, ?_, ?_⟩
  · have hleft : |a*c+b*d| ≤ a*|c|+b*|d| := by
      simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*c) (b*d)
    have hstrict : a*(|c|+s)+b*(|d|+r) < ell := by
      rcases eq_or_lt_of_le ha with he | hp
      · have ha0 : a=0 := he.symm
        have hb1 : b=1 := by linarith
        simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hd
      · have h₁ := mul_lt_mul_of_pos_left hc hp
        have h₂ := mul_le_mul_of_nonneg_left hd.le hb
        have he : a*ell+b*ell=ell := by rw [← add_mul, hab, one_mul]
        linarith
    nlinarith
  · convert hK hcl hdl ha hb hab using 1; module
  · convert hK hcr hdr ha hb hab using 1; module

lemma section_convex {K : Set E} (hK : Convex ℝ K) (e : E) (ell s : ℝ) :
    Convex ℝ (sectionDomain K e ell s) := by
  intro y hy z hz a b ha hb hab
  have h := section_mix hK e ell hy hz ha hb hab
  have hs : a*s+b*s=s := by rw [← add_mul, hab, one_mul]
  rwa [hs] at h

lemma line_segment_mem {K : Set E} (hK : Convex ℝ K) {y e : E} {c z : ℝ}
    (hleft : y+(c-1) • e ∈ K) (hright : y+(c+1) • e ∈ K)
    (hz : c-1 ≤ z ∧ z ≤ c+1) : y+z • e ∈ K := by
  have ha : 0 ≤ (c+1-z)/2 := by linarith [hz.2]
  have hb : 0 ≤ (z-c+1)/2 := by linarith [hz.1]
  have hab : (c+1-z)/2+(z-c+1)/2=1 := by ring
  convert hK hleft hright ha hb hab using 1; module

lemma section_symmetric {K : Set E} (hK : ∀ x ∈ K, -x ∈ K) (e : E) (ell s : ℝ) :
    ∀ y ∈ sectionDomain K e ell s, -y ∈ sectionDomain K e ell s := by
  intro y hy
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  refine ⟨-c,by simpa only [abs_neg] using hc,?_,?_⟩
  · convert hK _ hcr using 1; module
  · convert hK _ hcl using 1; module

lemma shifted_step {K : Set E} (hK : Convex ℝ K) (e : E)
    {y : E} (hy : y ∈ sectionDomain K e (5/2) 1) {q : ℝ} (hq : |q|≤1/4) :
    ∃ ε : ℝ, (ε = -1 ∨ ε = 1) ∧ y+(q+ε) • e ∈ K := by
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  have hca : |c|<3/2 := by linarith
  have hcb : -(3/2)<c ∧ c<3/2 := abs_lt.mp hca
  have hqb : -(1/4)≤q ∧ q≤1/4 := abs_le.mp hq
  rcases le_total q c with h | h
  · refine ⟨1,Or.inr rfl,line_segment_mem hK hcl hcr ?_⟩
    constructor <;> linarith [hcb.1,hcb.2,hqb.1,hqb.2]
  · refine ⟨-1,Or.inl rfl,line_segment_mem hK hcl hcr ?_⟩
    constructor <;> linarith [hcb.1,hcb.2,hqb.1,hqb.2]

lemma zero_mem_of_symmetric_convex {K : Set E} (hK : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty) : (0:E) ∈ K := by
  obtain ⟨x,hx⟩ := hne
  have h := hK hx (hsym x hx) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simpa only [smul_neg, add_neg_cancel] using h

end ShiftedSections

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement

section Layer
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

lemma layer_pair (a : X → U → ℝ≥0∞) (b : X → V → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) (hb : Measurable (Function.uncurry b)) :
    (∫⁻ x, (∫⁻ u, a x u ∂ν) * (∫⁻ v, b x v ∂ρ) ∂μ) =
      ∫⁻ u, ∫⁻ v, ∫⁻ x, a x u * b x v ∂μ ∂ρ ∂ν := by
  have hai (x : X) : Measurable (a x) := ha.comp measurable_prodMk_left
  have hbi (x : X) : Measurable (b x) := hb.comp measurable_prodMk_left
  simp_rw [← lintegral_mul_const _ (hai _), ← lintegral_const_mul _ (hbi _)]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro u
    apply lintegral_lintegral_swap
    exact ((ha.comp (measurable_fst.prodMk measurable_const)).mul
      (hb.comp (measurable_fst.prodMk measurable_snd))).aemeasurable
  · apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    exact (ha.comp (measurable_fst.fst.prodMk measurable_fst.snd)).mul
      (hb.comp (measurable_fst.fst.prodMk measurable_snd))

lemma layer_measurable (S : U → Set X) (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    Measurable (layer S ν) := by
  apply Measurable.lintegral_prod_right
  exact measurable_const.indicator hS

lemma layer_pair_sets (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2}) :
    (∫⁻ x, layer S ν x * layer T ρ x ∂μ) =
      ∫⁻ u, ∫⁻ v, μ (S u ∩ T v) ∂ρ ∂ν := by
  unfold layer
  rw [layer_pair (fun x u => (S u).indicator (fun _ => (1:ℝ≥0∞)) x)
    (fun x v => (T v).indicator (fun _ => (1:ℝ≥0∞)) x)
    (measurable_const.indicator hS) (measurable_const.indicator hT)]
  apply lintegral_congr
  intro u
  apply lintegral_congr
  intro v
  have hs : MeasurableSet (S u) := hS.preimage measurable_prodMk_right
  have ht : MeasurableSet (T v) := hT.preimage measurable_prodMk_right
  have he (x : X) : (S u).indicator (fun _ => (1:ℝ≥0∞)) x *
      (T v).indicator (fun _ => (1:ℝ≥0∞)) x = (S u ∩ T v).indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ S u <;> by_cases hy : x ∈ T v <;> simp [hx,hy]
  simp_rw [he]
  rw [lintegral_indicator (hs.inter ht), lintegral_one, Measure.restrict_apply_univ]

end Layer

lemma measure_inter_eq_min_of_nested {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S T : Set X) (h : S ⊆ T ∨ T ⊆ S) : μ (S ∩ T) = min (μ S) (μ T) := by
  rcases h with h | h
  · rw [inter_eq_left.mpr h, min_eq_left (measure_mono h)]
  · rw [inter_eq_right.mpr h, min_eq_right (measure_mono h)]

lemma centered_measurable (a : ℝ≥0∞) : MeasurableSet (centered a) :=
  measurableSet_lt measurable_id.abs measurable_const

lemma measure_centered {a : ℝ≥0∞} (ha : a ≠ ⊤) : volume (centered a) = a := by
  have he : centered a = Ioo (-(a.toReal/2)) (a.toReal/2) := by
    ext s
    change |s| < a.toReal / 2 ↔ -(a.toReal/2) < s ∧ s < a.toReal/2
    exact abs_lt
  rw [he, Real.volume_Ioo, show a.toReal/2 - -(a.toReal/2) = a.toReal by ring,
    ENNReal.ofReal_toReal ha]

lemma centered_mono {a b : ℝ≥0∞} (ha : a ≤ b) (hb : b ≠ ⊤) : centered a ⊆ centered b := by
  intro s hs
  exact hs.trans_le (div_le_div_of_nonneg_right (ENNReal.toReal_mono hb ha) (by norm_num))

lemma centered_inter {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    volume (centered a ∩ centered b) = min a b := by
  rcases le_total a b with h | h
  · rw [inter_eq_left.mpr (centered_mono h hb), measure_centered ha, min_eq_left h]
  · rw [inter_eq_right.mpr (centered_mono h ha), measure_centered hb, min_eq_right h]

lemma integral_abs_symmetric {r : ℝ} (hr : 0 ≤ r) :
    (∫ s : ℝ in -r..r, |s|) = r^2 := by
  have hl : (∫ s : ℝ in -r..0, |s|) = r^2/2 := by
    have he : (∫ s : ℝ in -r..0, |s|) = ∫ s : ℝ in -r..0, -s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : -r ≤ (0:ℝ))] at hx
      exact abs_of_nonpos hx.2
    rw [he, intervalIntegral.integral_neg, integral_id]
    ring
  have hu : (∫ s : ℝ in 0..r, |s|) = r^2/2 := by
    have he : (∫ s : ℝ in 0..r, |s|) = ∫ s : ℝ in 0..r, s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hr] at hx
      exact abs_of_nonneg hx.1
    rw [he, integral_id]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-r) 0) (continuous_abs.intervalIntegrable 0 r), hl, hu]
  ring

lemma heightMeasure_centered {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    heightMeasure (centered a) = a^2/4 := by
  have he : centered a = Ioo (-(a.toReal/2)) (a.toReal/2) := by
    ext s
    change |s| < a.toReal/2 ↔ -(a.toReal/2) < s ∧ s < a.toReal/2
    exact abs_lt
  have hi : IntegrableOn (fun s : ℝ => |s|) (centered a) := by
    rw [he]
    exact continuous_abs.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [heightMeasure, withDensity_apply _ (centered_measurable a),
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => abs_nonneg _))]
  rw [he, restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by linarith [ENNReal.toReal_nonneg (a := a)] : -(a.toReal/2) ≤ a.toReal/2),
    integral_abs_symmetric (by positivity)]
  rw [div_pow, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_pow
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]
  norm_num

lemma heightMeasure_centered_inter {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    heightMeasure (centered a ∩ centered b) = (min a b)^2/4 := by
  rcases le_total a b with h | h
  · rw [inter_eq_left.mpr (centered_mono h hb), heightMeasure_centered ha, min_eq_left h]
  · rw [inter_eq_right.mpr (centered_mono h ha), heightMeasure_centered hb, min_eq_right h]

section Rearranged
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

lemma measure_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    Measurable (fun u => μ (S u)) := by
  have he (u : U) : μ (S u) = ∫⁻ x, (S u).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
    have hs : MeasurableSet (S u) := hS.preimage measurable_prodMk_right
    rw [lintegral_indicator hs, lintegral_one, Measure.restrict_apply_univ]
  simp_rw [he]
  apply Measurable.lintegral_prod_left
  exact measurable_const.indicator hS

lemma centered_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    MeasurableSet {p : ℝ × U | p.1 ∈ centered (μ (S p.2))} := by
  exact measurableSet_lt measurable_fst.abs
    (((measure_family_measurable S hS).comp measurable_snd).ennreal_toReal.div_const 2)

lemma rearranged_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) : Measurable (rearranged S μ ν) :=
  layer_measurable _ (centered_family_measurable S hS)

lemma rearranged_pair (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤) :
    (∫⁻ s, rearranged S μ ν s * rearranged T μ ρ s) =
      ∫⁻ u, ∫⁻ v, min (μ (S u)) (μ (T v)) ∂ρ ∂ν := by
  unfold rearranged
  rw [layer_pair_sets _ _ (centered_family_measurable S hS) (centered_family_measurable T hT)]
  simp_rw [centered_inter (hfS _) (hfT _)]

lemma rearranged_inner_ge (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤) :
    (∫⁻ x, layer S ν x * layer T ρ x ∂μ) ≤
      ∫⁻ s, rearranged S μ ν s * rearranged T μ ρ s := by
  rw [layer_pair_sets S T hS hT, rearranged_pair S T hS hT hfS hfT]
  apply lintegral_mono
  intro u
  apply lintegral_mono
  intro v
  exact le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)

lemma rearranged_square (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hnest : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u) :
    (∫⁻ s, (rearranged S μ ν s)^2) = ∫⁻ x, (layer S ν x)^2 ∂μ := by
  simp only [pow_two]
  rw [rearranged_pair S S hS hS hfS hfS, layer_pair_sets S S hS hS]
  simp_rw [measure_inter_eq_min_of_nested μ _ _ (hnest _ _)]

lemma rearranged_height (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged S μ ν s)^2) =
      ∫⁻ u, ∫⁻ v, (min (μ (S u)) (μ (S v)))^2/4 ∂ν ∂ν := by
  have hm : Measurable (fun s : ℝ => (rearranged S μ ν s)^2) :=
    (rearranged_measurable (μ := μ) (ν := ν) S hS).pow_const 2
  have he := lintegral_withDensity_eq_lintegral_mul volume
    (f := fun s : ℝ => ENNReal.ofReal |s|) (g := fun s => (rearranged S μ ν s)^2)
    measurable_id.abs.ennreal_ofReal hm
  change (∫⁻ s, ((fun s : ℝ => ENNReal.ofReal |s|) *
    (fun s => (rearranged S μ ν s)^2)) s) = _
  rw [← he]
  change (∫⁻ s, (rearranged S μ ν s)^2 ∂heightMeasure) = _
  simp only [pow_two]
  unfold rearranged
  rw [layer_pair_sets _ _ (centered_family_measurable S hS) (centered_family_measurable S hS)]
  simp only [heightMeasure_centered_inter (hfS _) (hfS _), pow_two]

lemma prod_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    MeasurableSet {p : (X × X) × U | p.1 ∈ S p.2 ×ˢ S p.2} := by
  exact (hS.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
    (hS.preimage (measurable_fst.snd.prodMk measurable_snd))

lemma rearranged_height_pair (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hnest : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged S μ ν s)^2) =
      (∫⁻ p : X × X, (layer (fun u => S u ×ˢ S u) ν p)^2 ∂μ.prod μ)/4 := by
  rw [rearranged_height S hS hfS]
  simp_rw [ENNReal.div_eq_inv_mul, lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  congr 1
  simp only [pow_two]
  rw [layer_pair_sets _ _ (prod_family_measurable S hS) (prod_family_measurable S hS)]
  simp_rw [prod_inter_prod, Measure.prod_prod,
    measure_inter_eq_min_of_nested μ _ _ (hnest _ _)]

end Rearranged

section FunctionLayers
variable {X : Type*} [MeasurableSpace X]

lemma superlevel_measurable {f : X → ℝ} (hf : Measurable f) :
    MeasurableSet {p : X × ℝ | p.1 ∈ superlevel f p.2} :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hf.comp measurable_fst))

omit [MeasurableSpace X] in
lemma layer_superlevel (f : X → ℝ) (x : X) : layer (superlevel f) volume x = ENNReal.ofReal (f x) := by
  have he (u : ℝ) : (superlevel f u).indicator (fun _ => (1:ℝ≥0∞)) x =
      (Ioo 0 (f x)).indicator (fun _ => (1:ℝ≥0∞)) u := by
    by_cases h : 0 < u ∧ u < f x <;> simp [superlevel, h]
  simp_rw [layer, he]
  rw [lintegral_indicator measurableSet_Ioo, lintegral_one,
    Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]

omit [MeasurableSpace X] in
lemma superlevel_nested (f : X → ℝ) (u v : ℝ) :
    superlevel f u ⊆ superlevel f v ∨ superlevel f v ⊆ superlevel f u := by
  by_cases hu : 0 < u
  · by_cases hv : 0 < v
    · rcases le_total u v with h | h
      · exact Or.inr fun x hx => ⟨hu, h.trans_lt hx.2⟩
      · exact Or.inl fun x hx => ⟨hv, h.trans_lt hx.2⟩
    · exact Or.inr fun x hx => (hv hx.1).elim
  · exact Or.inl fun x hx => (hu hx.1).elim

omit [MeasurableSpace X] in
lemma layer_superlevel_prod (f : X → ℝ) (p : X × X) :
    layer (fun u => superlevel f u ×ˢ superlevel f u) volume p =
      ENNReal.ofReal (min (f p.1) (f p.2)) := by
  have he : (fun u => superlevel f u ×ˢ superlevel f u) =
      superlevel (fun q : X × X => min (f q.1) (f q.2)) := by
    funext u
    ext q
    simp only [superlevel, mem_prod, mem_ofPred_eq, lt_min_iff]
    tauto
  rw [he, layer_superlevel]

lemma function_rearranged_height (μ : Measure X) [SFinite μ] {f : X → ℝ}
    (hf : Measurable f) (hfinite : ∀ u, μ (superlevel f u) ≠ ⊤) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged (superlevel f) μ volume s)^2) =
      (∫⁻ x, ∫⁻ y, (ENNReal.ofReal (min (f x) (f y)))^2 ∂μ ∂μ)/4 := by
  rw [rearranged_height_pair _ (superlevel_measurable hf) hfinite (superlevel_nested f)]
  simp_rw [layer_superlevel_prod]
  congr 1
  exact lintegral_prod (μ := μ) (ν := μ) _
    (((hf.comp measurable_fst).min (hf.comp measurable_snd)).ennreal_ofReal.pow_const 2).aemeasurable

end FunctionLayers
end VerticalRearrangement

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement

section RealLayers
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma ae_finite_of_square {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) : ∀ᵐ x ∂μ, f x < ⊤ := by
  filter_upwards [ae_lt_top (hf.pow_const 2) hi] with x hx
  by_contra hn
  have he : f x = ⊤ := not_lt_top_iff.mp hn
  simp [he] at hx

lemma toReal_memLp {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) : MemLp (fun x => (f x).toReal) 2 μ := by
  apply (memLp_two_iff_integrable_sq hf.ennreal_toReal.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_pow] using
    integrable_toReal_of_lintegral_ne_top (hf.pow_const 2).aemeasurable hi

lemma integral_toReal_square {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) :
    (∫ x, (f x).toReal^2 ∂μ) = (∫⁻ x, (f x)^2 ∂μ).toReal := by
  simpa only [ENNReal.toReal_pow] using
    integral_toReal (hf.pow_const 2).aemeasurable (ae_lt_top (hf.pow_const 2) hi)

lemma lintegral_mul_ne_top_of_squares {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) (hgi : ∫⁻ x, (g x)^2 ∂μ ≠ ⊤) :
    ∫⁻ x, f x * g x ∂μ ≠ ⊤ := by
  have hi := ((toReal_memLp hf hfi).integrable_mul (toReal_memLp hg hgi)).lintegral_lt_top
  have he : (fun x => ENNReal.ofReal ((f x).toReal*(g x).toReal)) =ᵐ[μ]
      fun x => f x*g x := by
    filter_upwards [ae_finite_of_square hf hfi, ae_finite_of_square hg hgi] with x hx hy
    rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hx.ne hy.ne)]
  exact (lt_of_eq_of_lt (lintegral_congr_ae he).symm hi).ne

lemma integral_toReal_mul {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) (hgi : ∫⁻ x, (g x)^2 ∂μ ≠ ⊤) :
    (∫ x, (f x).toReal*(g x).toReal ∂μ) = (∫⁻ x, f x*g x ∂μ).toReal := by
  apply (integral_congr_ae (ae_of_all _ fun _ => ENNReal.toReal_mul.symm)).trans
  apply integral_toReal (hf.mul hg).aemeasurable
  filter_upwards [ae_finite_of_square hf hfi, ae_finite_of_square hg hgi] with x hx hy
  exact ENNReal.mul_lt_top hx hy

end RealLayers

lemma integral_sub_sq {Y : Type*} [MeasurableSpace Y] {ζ : Measure Y} {f g : Y → ℝ}
      (hf : MemLp f 2 ζ) (hg : MemLp g 2 ζ) :
      (∫ y, (f y-g y)^2 ∂ζ) = (∫ y, (f y)^2 ∂ζ)+(∫ y, (g y)^2 ∂ζ)-2*(∫ y, f y*g y ∂ζ) := by
  have hff : Integrable (fun y => f y^2) ζ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hgg : Integrable (fun y => g y^2) ζ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun y => f y*g y) ζ := hf.integrable_mul hg
  simp_rw [show ∀ y, (f y-g y)^2 = f y^2+g y^2-2*(f y*g y) by intro y; ring]
  have hsum : Integrable (fun y => f y^2+g y^2) ζ := hff.add hgg
  have htwo : Integrable (fun y => 2*(f y*g y)) ζ := hfg.const_mul 2
  rw [integral_sub hsum htwo, integral_add hff hgg, integral_const_mul]

section L2
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]
variable (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤)
    (hnS : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u)
    (hnT : ∀ u v, T u ⊆ T v ∨ T v ⊆ T u)
    (hiS : ∫⁻ x, (layer S ν x)^2 ∂μ ≠ ⊤)
    (hiT : ∫⁻ x, (layer T ρ x)^2 ∂μ ≠ ⊤)

include hS hfS hnS hiS in
lemma rearranged_real_memLp : MemLp (fun s => (rearranged S μ ν s).toReal) 2 volume := by
  apply toReal_memLp (rearranged_measurable (μ := μ) (ν := ν) S hS)
  simpa only [rearranged_square S hS hfS hnS] using hiS

include hS hfS hnS hiS in
lemma rearranged_real_square :
    (∫ s, (rearranged S μ ν s).toReal^2) = ∫ x, (layer S ν x).toReal^2 ∂μ := by
  rw [integral_toReal_square (rearranged_measurable (μ := μ) (ν := ν) S hS)
      (by simpa only [rearranged_square S hS hfS hnS] using hiS),
    integral_toReal_square (layer_measurable S hS) hiS,
    rearranged_square S hS hfS hnS]

include hS hT hfS hfT hnS hnT hiS hiT in
lemma rearranged_real_inner :
    (∫ x, (layer S ν x).toReal*(layer T ρ x).toReal ∂μ) ≤
      ∫ s, (rearranged S μ ν s).toReal*(rearranged T μ ρ s).toReal := by
  have hs := rearranged_measurable (μ := μ) (ν := ν) S hS
  have ht := rearranged_measurable (μ := μ) (ν := ρ) T hT
  have his : ∫⁻ s, (rearranged S μ ν s)^2 ≠ ⊤ := by simpa only [rearranged_square S hS hfS hnS] using hiS
  have hit : ∫⁻ s, (rearranged T μ ρ s)^2 ≠ ⊤ := by simpa only [rearranged_square T hT hfT hnT] using hiT
  rw [integral_toReal_mul (layer_measurable S hS) (layer_measurable T hT) hiS hiT,
    integral_toReal_mul hs ht his hit]
  exact ENNReal.toReal_mono (lintegral_mul_ne_top_of_squares hs ht his hit)
    (rearranged_inner_ge S T hS hT hfS hfT)

include hS hT hfS hfT hnS hnT hiS hiT in
lemma rearranged_real_difference :
    (∫ s, ((rearranged S μ ν s).toReal-(rearranged T μ ρ s).toReal)^2) ≤
      ∫ x, ((layer S ν x).toReal-(layer T ρ x).toReal)^2 ∂μ := by
  have hls := toReal_memLp (layer_measurable (ν := ν) S hS) hiS
  have hlt := toReal_memLp (layer_measurable (ν := ρ) T hT) hiT
  have hrs := rearranged_real_memLp S hS hfS hnS hiS
  have hrt := rearranged_real_memLp T hT hfT hnT hiT
  rw [integral_sub_sq hrs hrt, integral_sub_sq hls hlt, rearranged_real_square S hS hfS hnS hiS,
    rearranged_real_square T hT hfT hnT hiT]
  linarith [rearranged_real_inner S T hS hT hfS hfT hnS hnT hiS hiT]

end L2
end VerticalRearrangement

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Fibers
variable {X : Type*} [MeasurableSpace X]

lemma fiberLength_measurable {F : X × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : X × ℝ => volume (superlevel (fun s => F (p.1,s)) p.2)) := by
  apply measure_family_measurable
  change MeasurableSet {p : ℝ × (X × ℝ) | 0 < p.2.2 ∧ p.2.2 < F (p.2.1,p.1)}
  exact (measurableSet_lt measurable_const measurable_snd.snd).inter
    (measurableSet_lt measurable_snd.snd (hF.comp (measurable_snd.fst.prodMk measurable_fst)))

lemma fiberStar_measurable {F : X × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fiberStar F) := by
  unfold fiberStar rearranged layer
  apply Measurable.lintegral_prod_right
  apply measurable_const.indicator
  change MeasurableSet {p : (X × ℝ) × ℝ |
    |p.1.2| < (volume (superlevel (fun r => F (p.1.1,r)) p.2)).toReal / 2}
  exact measurableSet_lt measurable_fst.snd.abs
    (((fiberLength_measurable hF).comp (measurable_fst.fst.prodMk measurable_snd)).ennreal_toReal.div_const 2)

omit [MeasurableSpace X] in
lemma superlevel_measure_ne_top_of_strip {F : X × ℝ → ℝ} {ell : ℝ}
    (hstrip : ∀ p, ell ≤ |p.2| → F p = 0) (x : X) (u : ℝ) :
    volume (superlevel (fun s => F (x,s)) u) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := -ell) (b := ell)).ne
  apply measure_mono
  intro s hs
  change 0 < u ∧ u < F (x,s) at hs
  have h : |s| < ell := by
    by_contra hn
    rw [hstrip (x,s) (not_lt.mp hn)] at hs
    linarith [hs.1,hs.2]
  exact abs_lt.mp h

lemma fiberStar_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) (x : X) :
    (∫⁻ s, (fiberStar F (x,s))^2) = ∫⁻ s, (ENNReal.ofReal (F (x,s)))^2 := by
  change (∫⁻ s, (rearranged (superlevel (fun r => F (x,r))) volume volume s)^2) = _
  have hx : Measurable (fun s => F (x,s)) := hF.comp measurable_prodMk_left
  rw [rearranged_square _ (superlevel_measurable hx)
    (hfinite x) (superlevel_nested _)]
  simp only [layer_superlevel]

variable {μ : Measure X}
lemma fiberStar_total_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) :
    (∫⁻ p, (fiberStar F p)^2 ∂μ.prod volume) =
      ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume := by
  rw [lintegral_prod _ ((fiberStar_measurable hF).pow_const 2).aemeasurable,
    lintegral_prod _ (hF.ennreal_ofReal.pow_const 2).aemeasurable]
  apply lintegral_congr
  exact fiberStar_square hF hfinite

lemma fiberStar_toReal_memLp {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hi : ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume ≠ ⊤) :
    MemLp (fun p => (fiberStar F p).toReal) 2 (μ.prod volume) := by
  apply toReal_memLp (fiberStar_measurable hF)
  rwa [fiberStar_total_square hF hfinite]

lemma fiberStar_total_real_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hFn : ∀ p, 0 ≤ F p)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hi : ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume ≠ ⊤) :
    (∫ p, (fiberStar F p).toReal^2 ∂μ.prod volume) = ∫ p, F p^2 ∂μ.prod volume := by
  rw [integral_toReal_square (fiberStar_measurable hF)
      (by rwa [fiberStar_total_square hF hfinite]), fiberStar_total_square hF hfinite]
  simpa only [ENNReal.toReal_ofReal (hFn _)] using
    (integral_toReal_square hF.ennreal_ofReal hi).symm

omit [MeasurableSpace X] in
lemma fiberStar_eq_zero_of_measure_le {F : X × ℝ → ℝ} (x : X) (s : ℝ)
    (h : ∀ u, volume (superlevel (fun r => F (x,r)) u) ≤ ENNReal.ofReal (2*|s|)) :
    fiberStar F (x,s) = 0 := by
  unfold fiberStar rearranged layer
  have hz (u : ℝ) : (centered (volume (superlevel (fun r => F (x,r)) u))).indicator
      (fun _ => (1:ℝ≥0∞)) s = 0 := by
    apply indicator_of_notMem
    change ¬ |s| < (volume (superlevel (fun r => F (x,r)) u)).toReal/2
    have hh := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2*|s|) (h u)
    linarith
  simp only [hz,lintegral_zero]

lemma ofReal_square_integral_ne_top {F : X → ℝ} (hF : MemLp F 2 μ) (hFn : ∀ x,0 ≤ F x) :
    ∫⁻ x, (ENNReal.ofReal (F x))^2 ∂μ ≠ ⊤ := by
  have hh := ((memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF).lintegral_lt_top.ne
  simpa only [ENNReal.ofReal_pow (hFn _)] using hh

lemma fiberStar_difference {F G : X × ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ p,0 ≤ F p) (hGn : ∀ p,0 ≤ G p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hfG : ∀ x u,volume (superlevel (fun s => G (x,s)) u) ≠ ⊤)
    (x : X) (hiF : MemLp (fun s => F (x,s)) 2 volume)
    (hiG : MemLp (fun s => G (x,s)) 2 volume) :
    (∫ s, ((fiberStar F (x,s)).toReal-(fiberStar G (x,s)).toReal)^2) ≤
      ∫ s, (F (x,s)-G (x,s))^2 := by
  have hmF := superlevel_measurable (f := fun r => F (x,r)) (hF.comp measurable_prodMk_left)
  have hmG := superlevel_measurable (f := fun r => G (x,r)) (hG.comp measurable_prodMk_left)
  have hF' : ∫⁻ s, (layer (superlevel (fun r => F (x,r))) volume s)^2 ≠ ⊤ := by
    simpa only [layer_superlevel] using ofReal_square_integral_ne_top hiF (fun s => hFn (x,s))
  have hG' : ∫⁻ s, (layer (superlevel (fun r => G (x,r))) volume s)^2 ≠ ⊤ := by
    simpa only [layer_superlevel] using ofReal_square_integral_ne_top hiG (fun s => hGn (x,s))
  simpa only [fiberStar,layer_superlevel,ENNReal.toReal_ofReal (hFn _),
    ENNReal.toReal_ofReal (hGn _)] using
    rearranged_real_difference _ _ hmF hmG (hfF x) (hfG x)
      (superlevel_nested _) (superlevel_nested _) hF' hG'

lemma fiberStar_memLp {F : X × ℝ → ℝ} (hF : Measurable F) (hFn : ∀ p,0 ≤ F p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) :
    MemLp (fun p => (fiberStar F p).toReal) 2 (μ.prod volume) :=
  fiberStar_toReal_memLp hF hfF (ofReal_square_integral_ne_top hiF hFn)

lemma fiberStar_total_difference [SFinite μ] {F G : X × ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hFn : ∀ p,0 ≤ F p) (hGn : ∀ p,0 ≤ G p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hfG : ∀ x u,volume (superlevel (fun s => G (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) (hiG : MemLp G 2 (μ.prod volume)) :
    (∫ p, ((fiberStar F p).toReal-(fiberStar G p).toReal)^2 ∂μ.prod volume) ≤
      ∫ p, (F p-G p)^2 ∂μ.prod volume := by
  have hF2 := (memLp_two_iff_integrable_sq hiF.aestronglyMeasurable).mp hiF
  have hG2 := (memLp_two_iff_integrable_sq hiG.aestronglyMeasurable).mp hiG
  have hS := (fiberStar_memLp hF hFn hfF hiF).sub (fiberStar_memLp hG hGn hfG hiG)
  have hD := hiF.sub hiG
  have hS2 := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).mp hS
  have hD2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  simp only [Pi.sub_apply] at hS2 hD2
  rw [integral_prod _ hS2,integral_prod _ hD2]
  apply integral_mono_ae hS2.integral_prod_left hD2.integral_prod_left
  filter_upwards [hF2.prod_right_ae,hG2.prod_right_ae] with x hx hy
  exact fiberStar_difference hF hG hFn hGn hfF hfG x
    ((memLp_two_iff_integrable_sq (hF.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx)
    ((memLp_two_iff_integrable_sq (hG.comp measurable_prodMk_left).aestronglyMeasurable).mpr hy)

end Fibers
end VerticalRearrangement

end

section

open Set MeasureTheory
open scoped ENNReal
namespace ShiftedSections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma line_interval_mem {K : Set E} (hK : Convex ℝ K) {y e : E} {r t z : ℝ}
    (hr : y+r • e ∈ K) (ht : y+t • e ∈ K) (hz : z ∈ Icc r t) : y+z • e ∈ K := by
  have hc : Convex ℝ {a : ℝ | y+a • e ∈ K} := by
    intro a ha b hb u v hu hv huv
    change y+(u*a+v*b) • e ∈ K
    have hvu : v=1-u := by linarith
    subst v
    convert hK ha hb hu hv huv using 1; module
  exact hc.ordConnected.out hr ht hz

lemma section_mono {K : Set E} (hK : Convex ℝ K) (e : E) (ell : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    sectionDomain K e ell t ⊆ sectionDomain K e ell s := by
  rintro y ⟨c,hc,hl,hr⟩
  refine ⟨c,lt_of_le_of_lt (add_le_add_right hst _) hc,
    line_interval_mem hK hl hr ⟨?_,?_⟩,line_interval_mem hK hl hr ⟨?_,?_⟩⟩ <;> linarith

lemma section_of_fiber_pair {K : Set E} (hK : Convex ℝ K) {y e : E} {ell r t s : ℝ}
    (hr : |r| < ell) (ht : |t| < ell) (hry : y+r • e ∈ K) (hty : y+t • e ∈ K)
    (hs : 0 ≤ s) (hst : 2*s < t-r) : y ∈ sectionDomain K e ell s := by
  refine ⟨(r+t)/2,?_,line_interval_mem hK hry hty ⟨?_,?_⟩,
    line_interval_mem hK hry hty ⟨?_,?_⟩⟩
  · rw [← lt_sub_iff_add_lt,abs_lt]
    constructor
    · linarith [(abs_lt.mp hr).1]
    · linarith [(abs_lt.mp ht).2]
  all_goals linarith

lemma fiber_measure_le_of_not_section {K : Set E} (hK : Convex ℝ K)
    {y e : E} {ell s : ℝ} (hs : 0 ≤ s) (hy : y ∉ sectionDomain K e ell s) :
    volume {r : ℝ | |r| < ell ∧ y+r • e ∈ K} ≤ ENNReal.ofReal (2*s) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro r hr t ht
  rw [Real.dist_eq]
  by_contra! hh
  rcases lt_or_ge r t with hrt | htr
  · rw [abs_of_nonpos (sub_nonpos.mpr hrt.le)] at hh
    exact hy (section_of_fiber_pair hK hr.1 ht.1 hr.2 ht.2 hs (by linarith))
  · rw [abs_of_nonneg (sub_nonneg.mpr htr)] at hh
    exact hy (section_of_fiber_pair hK ht.1 hr.1 ht.2 hr.2 hs hh)

lemma section_bounded {K : Set E} (hK : Bornology.IsBounded K) (e : E) {ell s : ℝ}
    (hs : 0 ≤ s) : Bornology.IsBounded (sectionDomain K e ell s) := by
  obtain ⟨R,hR⟩ := hK.subset_closedBall (0:E)
  apply Metric.isBounded_iff_subset_closedBall (0:E) |>.mpr
  refine ⟨R+|ell| * ‖e‖,?_⟩
  rintro y ⟨c,hc,hl,hr⟩
  have hcs : |c-s| < ell := by
    have hh := abs_sub c s
    rw [abs_of_nonneg hs] at hh
    exact hh.trans_lt hc
  have he : ‖(c-s) • e‖ ≤ |ell| * ‖e‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcs.le.trans (le_abs_self ell)) (norm_nonneg e)
  have hm : ‖y+(c-s) • e‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hl
  rw [Metric.mem_closedBall,dist_zero_right]
  calc
    ‖y‖ = ‖(y+(c-s) • e)-(c-s) • e‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖y+(c-s) • e‖+‖(c-s) • e‖ := norm_sub_le _ _
    _ ≤ R+|ell| * ‖e‖ := add_le_add hm he

lemma fiberStar_supported {K : Set E} (hK : Convex ℝ K) {e : E} {ell : ℝ}
    [MeasurableSpace E] {F : E × ℝ → ℝ}
    (hF : ∀ p, p.1+p.2 • e ∉ K ∨ ell ≤ |p.2| → F p = 0)
    {y : E} {s : ℝ} (hy : y ∉ sectionDomain K e ell |s|) :
    VerticalRearrangement.fiberStar F (y,s) = 0 := by
  apply VerticalRearrangement.fiberStar_eq_zero_of_measure_le
  intro u
  apply le_trans (measure_mono ?_) (fiber_measure_le_of_not_section hK (abs_nonneg s) hy)
  intro r hr
  change 0 < u ∧ u < F (y,r) at hr
  have hnot : ¬ (y+r • e ∉ K ∨ ell ≤ |r|) := by
    intro hn
    rw [hF (y,r) hn] at hr
    linarith [hr.1,hr.2]
  push Not at hnot
  exact ⟨hnot.2,hnot.1⟩

end ShiftedSections

end

section

open Set
namespace EuclideanSteinitz

lemma convex_supporting_line {J : Set ℝ} {h : ℝ → ℝ} (hc : ConvexOn ℝ J h)
    (hm : MonotoneOn h J) (h0 : 0 ∈ J) (h1 : 1 ∈ J)
    (hr : ∃ r ∈ J,1 < r) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ x ∈ J, h 1+a*(x-1) ≤ h x := by
  obtain ⟨r,hrJ,hr1⟩ := hr
  let L : Set ℝ := {a | ∃ x ∈ J,x<1 ∧ a=slope h x 1}
  have hL0 : slope h 0 1 ∈ L := ⟨0,h0,by norm_num,rfl⟩
  have hLne : L.Nonempty := ⟨_,hL0⟩
  have hLb : BddAbove L := by
    refine ⟨slope h 1 r,?_⟩
    rintro a ⟨x,hx,hx1,rfl⟩
    simpa only [slope_def_field] using hc.slope_mono_adjacent hx hrJ hx1 hr1
  refine ⟨sSup L,?_,?_⟩
  · have hh := le_csSup hLb hL0
    have hm01 := hm h0 h1 (by norm_num : (0:ℝ)≤1)
    simp only [slope_def_field,sub_zero,div_one] at hh
    linarith
  · intro x hx
    rcases lt_trichotomy x 1 with hx1 | rfl | h1x
    · have hh := le_csSup hLb (show slope h x 1 ∈ L from ⟨x,hx,hx1,rfl⟩)
      rw [slope_def_field,div_le_iff₀ (by linarith : 0 < 1-x)] at hh
      nlinarith
    · simp
    · have hh : sSup L ≤ slope h 1 x := by
        apply csSup_le hLne
        rintro a ⟨y,hy,hy1,rfl⟩
        simpa only [slope_def_field] using hc.slope_mono_adjacent hy hx hy1 h1x
      rw [slope_def_field,le_div_iff₀ (by linarith : 0 < x-1)] at hh
      linarith

end EuclideanSteinitz

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

lemma activeHeights_convex {K : Set (EuclideanSpace ℝ ι)} (hK : Convex ℝ K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) : Convex ℝ (activeHeights K e ell) := by
  rintro s ⟨hs,ys,hys⟩ t ⟨ht,yt,hyt⟩ a b ha hb hab
  exact ⟨add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht),
    ⟨a • ys+b • yt,section_mix hK e ell hys hyt ha hb hab⟩⟩

lemma sectionNorm_pos {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : 0 < sectionNorm K hKo e ell s v := by
  let D := sectionDomain K e ell s
  have hDb := section_bounded hKb e (ell := ell) hs.1
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  apply HeatL2.compressed_norm_pos D (section_open hKo e ell s).measurableSet
  exact (section_open hKo e ell s).measure_pos volume hs.2

lemma sectionNorm_le_one {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell s : ℝ) (v : ι → ℝ≥0) : sectionNorm K hKo e ell s v ≤ 1 :=
  HeatL2.compressedHeat_norm_le_one _ _ _ _ _

lemma sectionRate_nonneg {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : 0 ≤ sectionRate K hKo e ell v s := by
  exact neg_nonneg.mpr (Real.log_nonpos (sectionNorm_pos hKo hKb e ell v hs).le
    (sectionNorm_le_one hKo e ell s v))

lemma sectionRate_monotone {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K) (e : EuclideanSpace ℝ ι)
    (ell : ℝ) (v : ι → ℝ≥0) : MonotoneOn (sectionRate K hKo e ell v) (activeHeights K e ell) := by
  intro s hs t ht hst
  apply neg_le_neg
  apply Real.log_le_log (sectionNorm_pos hKo hKb e ell v ht)
  exact HeatL2.compressed_norm_mono_domain _ _ _ _ (section_mono hKc e ell hs.1 hst) _ _ _

lemma sectionRate_convex {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K) (e : EuclideanSpace ℝ ι)
    (ell : ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    ConvexOn ℝ (activeHeights K e ell) (sectionRate K hKo e ell v) := by
  refine ⟨activeHeights_convex hKc e ell,?_⟩
  intro s hs r hr a b ha hb hab
  have hbe : a=1-b := by linarith
  have hb1 : b ∈ Icc (0:ℝ) 1 := ⟨hb,by linarith⟩
  have hsr := activeHeights_convex hKc e ell hs hr ha hb hab
  have hh := GaussianKernel.compressed_norm_logconcave v hv
    (section_open hKo e ell s) (section_open hKo e ell r)
    (section_open hKo e ell (a*s+b*r))
    (section_bounded hKb e hs.1) (section_bounded hKb e hr.1)
    (section_bounded hKb e hsr.1) (section_convex hKc e ell s)
    (section_convex hKc e ell r) (section_convex hKc e ell (a*s+b*r))
    hs.2 hr.2 hb1 (fun y hy z hz => by
      rw [← hbe]
      exact section_mix hKc e ell hy hz ha hb hab)
  change sectionNorm K hKo e ell s v^(1-b)*sectionNorm K hKo e ell r v^b ≤
    sectionNorm K hKo e ell (a*s+b*r) v at hh
  rw [← hbe] at hh
  have hsp := sectionNorm_pos hKo hKb e ell v hs
  have hrp := sectionNorm_pos hKo hKb e ell v hr
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hsp _) (Real.rpow_pos_of_pos hrp _)) hh
  rw [Real.log_mul (Real.rpow_pos_of_pos hsp a).ne' (Real.rpow_pos_of_pos hrp b).ne',
    Real.log_rpow hsp,Real.log_rpow hrp] at hlog
  change -Real.log (sectionNorm K hKo e ell (a*s+b*r) v) ≤
    a*(-Real.log (sectionNorm K hKo e ell s v))+b*(-Real.log (sectionNorm K hKo e ell r v))
  linarith

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.SectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heat and energy inequalities for affine sections. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section RealFunctions
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma complexLp_coe (f : X → ℝ) (hf : MemLp f 2 μ) :
    (complexLp f hf : X → ℂ) =ᵐ[μ] fun x => (f x:ℂ) := MemLp.coeFn_toLp _

lemma complexLp_norm_sq (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖complexLp f hf‖^2 = ∫ x,f x^2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [complexLp_coe f hf] with x hx
  simp only [hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma nonnegRepresentative_measurable (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    Measurable (nonnegRepresentative D hD f) :=
  (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.norm.measurable.indicator hD

lemma nonnegRepresentative_nonneg (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) (x : X) :
    0 ≤ nonnegRepresentative D hD f x := by
  exact indicator_nonneg (fun _ _ => norm_nonneg _) x

lemma nonnegRepresentative_zero (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    {x : X} (hx : x ∉ D) : nonnegRepresentative D hD f x=0 := indicator_of_notMem hx _

lemma nonnegRepresentative_ae (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : nonnegRepresentative D hD f =ᵐ[μ] fun x => ‖f x‖ := by
  filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk,hf] with x hx hfx
  by_cases hxd : x ∈ D
  · simp only [nonnegRepresentative,indicator_of_mem hxd,hx]
  · simp only [nonnegRepresentative,indicator_of_notMem hxd,hfx hxd,norm_zero]

lemma nonnegRepresentative_memLp (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : MemLp (nonnegRepresentative D hD f) 2 μ :=
  (Lp.memLp f).norm.ae_eq (nonnegRepresentative_ae D hD f hf).symm

lemma nonnegRepresentative_square (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : (∫ x,nonnegRepresentative D hD f x^2 ∂μ)=‖f‖^2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [nonnegRepresentative_ae D hD f hf] with x hx
  rw [hx]

end RealFunctions

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma realDistance_eq (f : E → ℝ) (hf : MemLp f 2 volume) (a : E) :
    realDistance f a = ‖translate a (complexLp f hf)-complexLp f hf‖^2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translate a (complexLp f hf)) (complexLp f hf),
    translate_coe a (complexLp f hf),complexLp_coe f hf,
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (complexLp_coe f hf)]
    with x hsub htr hx hxa
  simp only [Function.comp_apply] at hxa
  simp only [hsub,Pi.sub_apply,htr,hx,hxa,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]

omit [FiniteDimensional ℝ F] in
lemma realDistance_integrable (f : E → ℝ) (hf : MemLp f 2 volume) (A : F →L[ℝ] E)
    (ν : Measure F) [IsFiniteMeasure ν] : Integrable (fun z => realDistance f (A z)) ν := by
  simp_rw [realDistance_eq f hf]
  exact integrable_difference_sq A ν _

lemma realEnergy_eq (f : E → ℝ) (hf : MemLp f 2 volume) (A : F →L[ℝ] E) :
    (1/2:ℝ)*(∫ z,realDistance f (A z) ∂ProbabilityTheory.stdGaussian F) =
      energy (gaussianSymbol A) (complexLp f hf) := by
  rw [gaussian_energy_difference]
  simp_rw [realDistance_eq f hf]

lemma norm_representative_distance_le (f : Lp ℂ 2 (volume : Measure E))
    (g : E → ℝ) (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖) (a : E) :
    realDistance g a ≤ ‖translate a f-f‖^2 := by
  have hgi := ((hg.comp_measurePreserving (measurePreserving_add_right volume a)).sub hg)
  have hgsq := (memLp_two_iff_integrable_sq hgi.aestronglyMeasurable).mp hgi
  have hfm := (Lp.memLp (translate a f-f)).norm
  have hfint := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hfm
  simp only [Pi.sub_apply,Function.comp_apply] at hgsq
  rw [realDistance,norm_sq_integral]
  apply integral_mono_ae hgsq hfint
  filter_upwards [he,(measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp he,
    Lp.coeFn_sub (translate a f) f,translate_coe a f] with x hx hxa hsub htr
  simp only [Function.comp_apply] at hxa
  simp only [hx,hxa,hsub,Pi.sub_apply,htr]
  apply sq_le_sq.mpr
  simpa only [abs_norm] using abs_norm_sub_norm_le (f (x+a)) (f x)

end Spatial
end HeatL2

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace HeatL2
section Slice
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma horizontal_translate_preserving (a : E) :
    MeasurePreserving (fun p : E × ℝ => (p.1+a,p.2))
      ((volume : Measure E).prod volume) (volume.prod volume) := by
  exact (measurePreserving_add_right volume a).prod (MeasurePreserving.id volume)

lemma horizontal_difference_integrable (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    Integrable (fun q : F × (E × ℝ) => (G (q.2.1+A q.1,q.2.2)-G q.2)^2)
      (ν.prod ((volume : Measure E).prod volume)) := by
  have hp : MeasurePreserving (fun q : F × (E × ℝ) => (q.1,(q.2.1+A q.1,q.2.2)))
      (ν.prod (volume.prod volume)) (ν.prod (volume.prod volume)) :=
    (MeasurePreserving.id ν).skew_product (by fun_prop)
      (ae_of_all _ fun z => (horizontal_translate_preserving (A z)).map_eq)
  have h₀ : MemLp (fun q : F × (E × ℝ) => G q.2) 2 (ν.prod (volume.prod volume)) :=
    hG.comp_measurePreserving measurePreserving_snd
  have h₁ := h₀.comp_measurePreserving hp
  have hd := h₁.sub h₀
  exact (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd

lemma slice_memLp (G : E × ℝ → ℝ) (hm : Measurable G)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) :
    ∀ᵐ s ∂(volume : Measure ℝ), MemLp (fun x => G (x,s)) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG
  filter_upwards [hi.prod_left_ae] with s hs
  exact (memLp_two_iff_integrable_sq (hm.comp (by fun_prop)).aestronglyMeasurable).mpr hs

lemma sliceEnergy_integrable (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] : Integrable (sliceEnergy ν A G) volume := by
  have hi := horizontal_difference_integrable G hG A ν
  have ha := (measurePreserving_prodAssoc ν (volume : Measure E)
    (volume : Measure ℝ)).integrable_comp_of_integrable hi
  have hk := ha.integral_prod_right
  apply (hk.const_mul (1/2:ℝ)).congr
  filter_upwards [ha.prod_left_ae] with s hs
  dsimp [sliceEnergy,realDistance]
  congr 1
  exact integral_prod _ hs

lemma integral_sliceEnergy (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    (∫ s,sliceEnergy ν A G s) = (1/2:ℝ) * ∫ z,
      ∫ p,(G (p.1+A z,p.2)-G p)^2 ∂((volume : Measure E).prod volume) ∂ν := by
  have hi := horizontal_difference_integrable G hG A ν
  have hp := measurePreserving_prodAssoc ν (volume : Measure E) (volume : Measure ℝ)
  have ha := hp.integrable_comp_of_integrable hi
  unfold sliceEnergy
  rw [integral_const_mul]
  congr 1
  calc
    (∫ s,∫ z,realDistance (fun x => G (x,s)) (A z) ∂ν) =
        ∫ s,∫ q : F × E,(G (q.2+A q.1,s)-G (q.2,s))^2 ∂ν.prod volume := by
      apply integral_congr_ae
      filter_upwards [ha.prod_left_ae] with s hs
      exact (integral_prod _ hs).symm
    _ = ∫ q : (F × E) × ℝ,(G (q.1.2+A q.1.1,q.2)-G (q.1.2,q.2))^2
        ∂(ν.prod volume).prod volume := (integral_prod_symm _ ha).symm
    _ = ∫ q : F × (E × ℝ),(G (q.2.1+A q.1,q.2.2)-G q.2)^2
        ∂ν.prod (volume.prod volume) := hp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
          (fun q : F × (E × ℝ) => (G (q.2.1+A q.1,q.2.2)-G q.2)^2)
    _ = _ := integral_prod _ hi

lemma integral_sliceEnergy_le {G : E × ℝ → ℝ}
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (A : F →L[ℝ] E)
    (hc : ∀ a : E,(∫ p,(G (p.1+a,p.2)-G p)^2 ∂(volume : Measure E).prod volume) ≤ realDistance f a) :
    (∫ s,sliceEnergy (ProbabilityTheory.stdGaussian F) A G s) ≤
      energy (gaussianSymbol A) (complexLp f hf) := by
  rw [integral_sliceEnergy G hG,← realEnergy_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact integral_mono (horizontal_difference_integrable G hG A _).integral_prod_left
    (realDistance_integrable f hf A _) (fun z => hc (A z))

end Slice
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

lemma sliceMass_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume)) : Integrable (sliceMass G) volume :=
  ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG).integral_prod_right

lemma integral_sliceMass {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume)) :
    (∫ s,sliceMass G s) = ∫ p,G p^2 ∂(volume : Measure (EuclideanSpace ℝ ι)).prod volume :=
  (integral_prod_symm _ ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG)).symm

lemma sliceMass_height_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) :
    Integrable (fun s => |s| *sliceMass G s) volume := by
  have hi := hH.integral_prod_right
  simpa only [sliceMass,integral_const_mul] using hi

lemma integral_sliceMass_height {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) :
    (∫ s,|s| *sliceMass G s) = ∫ p,|p.2| *G p^2 ∂(volume : Measure (EuclideanSpace ℝ ι)).prod volume := by
  rw [integral_prod_symm _ hH]
  simp only [sliceMass,integral_const_mul]

lemma height_above_one {K : Set (EuclideanSpace ℝ ι)} (e : EuclideanSpace ℝ ι) (ell : ℝ)
    {G : EuclideanSpace ℝ ι × ℝ → ℝ} (hG : MemLp G 2 (volume.prod volume))
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1)
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hh : 1 < ∫ p,|p.2| *G p^2 ∂volume.prod volume)
    (hs : ∀ p,p.1 ∉ sectionDomain K e ell |p.2| → G p=0) :
    ∃ r ∈ activeHeights K e ell,1 < r := by
  have hp : ∃ p : EuclideanSpace ℝ ι × ℝ, 1 < |p.2| ∧ G p ≠ 0 := by
    by_contra! he
    have hle : ∀ p : EuclideanSpace ℝ ι × ℝ, |p.2| *G p^2 ≤ G p^2 := by
      intro p
      by_cases hp : 1 < |p.2|
      · simp only [he p hp,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
      · exact mul_le_of_le_one_left (sq_nonneg _) (le_of_not_gt hp)
    have hi := integral_mono hH ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG) hle
    rw [hn] at hi
    linarith
  obtain ⟨p,hp,hpn⟩ := hp
  refine ⟨|p.2|,⟨abs_nonneg _,⟨p.1,?_⟩⟩,hp⟩
  by_contra hx
  exact hpn (hs p hx)

lemma activeHeights_contains_one {K : Set (EuclideanSpace ℝ ι)} (hK : Convex ℝ K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) (hr : ∃ r ∈ activeHeights K e ell,1 < r) :
    (0:ℝ) ∈ activeHeights K e ell ∧ (1:ℝ) ∈ activeHeights K e ell := by
  obtain ⟨r,hr,hr1⟩ := hr
  obtain ⟨y,hy⟩ := hr.2
  exact ⟨⟨le_refl 0,⟨y,section_mono hK e ell (le_refl 0) hr.1 hy⟩⟩,
    ⟨by norm_num,⟨y,section_mono hK e ell (by norm_num) hr1.le hy⟩⟩⟩

lemma activeHeights_lt {K : Set (EuclideanSpace ℝ ι)} (e : EuclideanSpace ℝ ι) (ell : ℝ)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : s < ell := by
  obtain ⟨y,c,hc,_,_⟩ := hs.2
  linarith [abs_nonneg c]

end ShiftedSections

end

section

open MeasureTheory Set
open scoped ComplexInnerProductSpace
namespace HeatL2

lemma loss_bounded_lower {t R L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) (hRL : R ≤ L) :
    t/(1+t*L)*R ≤ max 0 (loss (t*R)) := by
  have hd : 0 < 1+t*L := by positivity
  by_cases hR : 0 ≤ R
  · apply le_trans _ (le_max_right _ _)
    apply le_trans _ (loss_lower (mul_nonneg ht.le hR))
    calc
      t/(1+t*L)*R = (t*R)/(1+t*L) := by ring
      _ ≤ (t*R)/(1+t*R) := div_le_div_of_nonneg_left (mul_nonneg ht.le hR)
        (by positivity) (by nlinarith)
  · apply le_trans _ (le_max_left _ _)
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht.le hd.le) (le_of_not_ge hR)

section Affine
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma compressed_norm_smalltime (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg ht.le (hn ξ))‖ ≤
      ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖^t := by
  have hh := compressed_norm_rpow D hD w hw hn ht ht1
  simp only [one_mul] at hh
  simpa only [one_div,inv_inv] using
    (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (norm_nonneg _) (one_div_pos.mpr ht)).mpr hh

lemma energy_lower_rate (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    (hnorm : 0 < ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hR : R ≤ -Real.log ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    loss (t*R)*‖f‖^2 ≤ energy (fun ξ => t*w ξ) f := by
  have hs := compressed_norm_smalltime D hD w hw hn ht ht1
  have he : ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖^t ≤ Real.exp (-(t*R)) := by
    rw [Real.rpow_def_of_pos hnorm]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := form_le_norm D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg ht.le (hn ξ)) hf
  have hb := mul_le_mul_of_nonneg_right (hs.trans he) (sq_nonneg ‖f‖)
  dsimp [loss]
  nlinarith

lemma energy_lower_affine (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    (hnorm : 0 < ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {t R L : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hL : 0 ≤ L) (hRL : R ≤ L)
    (hR : R ≤ -Real.log ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    (t/(1+t*L)*R)*‖f‖^2 ≤ energy (fun ξ => t*w ξ) f := by
  have hh := loss_bounded_lower ht hL hRL
  apply (mul_le_mul_of_nonneg_right hh (sq_nonneg ‖f‖)).trans
  rw [max_mul_of_nonneg _ _ (sq_nonneg ‖f‖),zero_mul]
  exact max_le (energy_nonneg _ (fun ξ => mul_nonneg ht.le (hn ξ)) f)
    (energy_lower_rate D hD w hw hn hnorm ht ht1 hR hf)

end Affine
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
open HeatL2
variable {ι : Type*} [Fintype ι]

lemma sliceMass_affine_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume))
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) (h a : ℝ) :
    Integrable (fun s => (h+a*(|s|-1))*sliceMass G s) volume := by
  have he : (fun s => (h+a*(|s|-1))*sliceMass G s) =
      (fun s => (h-a)*sliceMass G s+a*(|s| *sliceMass G s)) := by ext s; ring
  rw [he]
  exact ((sliceMass_integrable hG).const_mul (h-a)).add
    ((sliceMass_height_integrable hH).const_mul a)

lemma integral_sliceMass_affine {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume))
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1) (h a : ℝ) :
    (∫ s,(h+a*(|s|-1))*sliceMass G s) = h+a*((∫ p,|p.2| *G p^2 ∂volume.prod volume)-1) := by
  have he : (fun s => (h+a*(|s|-1))*sliceMass G s) =
      (fun s => (h-a)*sliceMass G s+a*(|s| *sliceMass G s)) := by ext s; ring
  rw [he,integral_add ((sliceMass_integrable hG).const_mul _) ((sliceMass_height_integrable hH).const_mul _),
    integral_const_mul,integral_const_mul,integral_sliceMass hG,hn,integral_sliceMass_height hH]
  ring

lemma integrated_section_rate {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) {ell : ℝ} (hell : 0 ≤ ell)
    (v : ι → ℝ≥0) {h a : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hline : ∀ r ∈ activeHeights K e ell,h+a*(r-1) ≤ sectionRate K hKo e ell v r)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hA : gaussianSymbol A = fun ξ => t*GaussianKernel.symbol v ξ)
    {G : EuclideanSpace ℝ ι × ℝ → ℝ} (hGm : Measurable G)
    (hG : MemLp G 2 (volume.prod volume))
    (hGs : ∀ p,p.1 ∉ sectionDomain K e ell |p.2| → G p=0)
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1)
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hheight : 1 ≤ ∫ p,|p.2| *G p^2 ∂volume.prod volume) :
    t/(1+t*(h+a*ell))*h ≤ ∫ s,sliceEnergy (ProbabilityTheory.stdGaussian _) A G s := by
  let L := h+a*ell
  have hL : 0 ≤ L := add_nonneg hh (mul_nonneg ha hell)
  have hC : 0 ≤ t/(1+t*L) := by positivity
  have hint := (sliceMass_affine_integrable hG hH h a).const_mul (t/(1+t*L))
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ),
      (t/(1+t*L))*((h+a*(|s|-1))*sliceMass G s) ≤
        sliceEnergy (ProbabilityTheory.stdGaussian _) A G s := by
    filter_upwards [slice_memLp G hGm hG] with s hs
    by_cases hact : |s| ∈ activeHeights K e ell
    · let D := sectionDomain K e ell |s|
      have hD : MeasurableSet D := (section_open hKo e ell |s|).measurableSet
      have hsupp : complexLp (fun x => G (x,s)) hs ∈ supported D := by
        filter_upwards [complexLp_coe (fun x => G (x,s)) hs] with x hx hn
        rw [hx,hGs (x,s) hn,Complex.ofReal_zero]
      have hb := energy_lower_affine D hD (GaussianKernel.symbol v)
        (GaussianKernel.symbol_continuous v).measurable (GaussianKernel.symbol_nonneg v)
        (sectionNorm_pos hKo hKb e ell v hact) ht ht1 hL
        (show h+a*(|s|-1) ≤ L by
          have := activeHeights_lt e ell hact
          dsimp [L]
          nlinarith)
        (hline |s| hact) hsupp
      rw [complexLp_norm_sq,← hA,← realEnergy_eq] at hb
      simpa only [sliceMass,sliceEnergy,mul_assoc] using hb
    · have hz : ∀ x,G (x,s)=0 := by
        intro x
        apply hGs (x,s)
        intro hx
        exact hact ⟨abs_nonneg _,⟨x,hx⟩⟩
      simp only [sliceMass,sliceEnergy,realDistance,hz,sub_self,zero_pow (by norm_num : 2 ≠ 0),
        integral_zero,mul_zero,le_refl]
  have hInt := integral_mono_ae hint (sliceEnergy_integrable G hG A _) hbound
  rw [integral_const_mul,integral_sliceMass_affine hG hH hn h a] at hInt
  apply le_trans _ hInt
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith

end ShiftedSections

end

section

open MeasureTheory Set FourierTransform
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
section Energy
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma energy_sum_dilate_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → E → ℝ)
    (hc : ∀ i ∈ s,1 ≤ c i) (hw : ∀ i ∈ s,AEStronglyMeasurable (w i) volume)
    (hn : ∀ i ∈ s,∀ ξ,0 ≤ w i ξ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy (fun ξ => ∑ i ∈ s,c i*w i ξ) f ≤ ∑ i ∈ s,c i*energy (w i) f := by
  have hi i (h : i ∈ s) := (integrable_energy (w i) (hw i h) (hn i h) f).const_mul (c i)
  have hw' : AEStronglyMeasurable (fun ξ => ∑ i ∈ s,c i*w i ξ) volume :=
    s.aestronglyMeasurable_fun_sum fun i hi => (hw i hi).const_mul (c i)
  have hn' ξ : 0 ≤ ∑ i ∈ s,c i*w i ξ := Finset.sum_nonneg fun i hi =>
    mul_nonneg (le_trans zero_le_one (hc i hi)) (hn i hi ξ)
  have he : (∑ i ∈ s,c i*energy (w i) f) =
      ∫ ξ,∑ i ∈ s,c i*(loss (w i ξ)*‖(𝓕 f) ξ‖^2) := by
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  rw [he]
  apply integral_mono (integrable_energy _ hw' hn' f) (integrable_finsetSum s hi)
  intro ξ
  simpa only [← mul_assoc,← Finset.sum_mul] using
    mul_le_mul_of_nonneg_right (loss_sum_dilate_le s c (fun i => w i ξ) hc
      (fun i hi => hn i hi ξ)) (sq_nonneg ‖(𝓕 f) ξ‖)

lemma norm_representative_energy_le (f : Lp ℂ 2 (volume : Measure E))
    (g : E → ℝ) (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖)
    (A : F →L[ℝ] E) : energy (gaussianSymbol A) (complexLp g hg) ≤ energy (gaussianSymbol A) f := by
  rw [← realEnergy_eq,gaussian_energy_difference]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact integral_mono (realDistance_integrable g hg A _) (integrable_difference_sq A _ f)
    (fun z => norm_representative_distance_le f g hg he _)

end Energy
namespace Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma directionalSymbol_single (i : ι) : directionalSymbol (EuclideanSpace.single i (1:ℝ))=coordSymbol i := by
  ext ξ
  simp only [directionalSymbol,coordSymbol,EuclideanSpace.inner_single_left,map_one,one_mul]

omit [DecidableEq ι] in
lemma symbol_scaled_sum (v : ι → ℝ≥0) (t : ℝ) :
    (fun ξ => t*GaussianKernel.symbol v ξ) = fun ξ => ∑ i,(t*(v i:ℝ)/2)*coordSymbol i ξ := by
  ext ξ
  unfold GaussianKernel.symbol coordSymbol
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
lemma energy_weighted_le (v : ι → ℝ≥0) {η t : ℝ} (hη : 0 < η)
    (hηt : ∀ i,η ≤ t*(v i:ℝ)/2) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (fun ξ => t*GaussianKernel.symbol v ξ) f ≤
      ∑ i,(t*(v i:ℝ)/(2*η))*energy (fun ξ => η*coordSymbol i ξ) f := by
  have he : (fun ξ => t*GaussianKernel.symbol v ξ) =
      fun ξ => ∑ i,(t*(v i:ℝ)/(2*η))*(η*coordSymbol i ξ) := by
    rw [symbol_scaled_sum]
    ext ξ
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [he]
  apply energy_sum_dilate_le
  · intro i _
    rw [le_div_iff₀ (by positivity : 0 < 2*η)]
    linarith [hηt i]
  · intro i _
    exact ((coordSymbol_continuous i).const_mul η).aestronglyMeasurable
  · intro i _ ξ
    exact mul_nonneg hη.le (coordSymbol_nonneg i ξ)

lemma norm_representative_diagonal_energy_le (v : ι → ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (g : EuclideanSpace ℝ ι → ℝ)
    (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖) :
    energy (GaussianKernel.symbol v) (complexLp g hg) ≤ energy (GaussianKernel.symbol v) f := by
  rw [← GaussianKernel.symbol_eq]
  exact norm_representative_energy_le f g hg he _

end Diagonal
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma simultaneous_real_density {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D}
    {c η ε : ℝ} (hB : Bound D hD c) (hη : 0 < η) (hε : 0 < ε) :
    ∃ f : EuclideanSpace ℝ ι → ℝ, Measurable f ∧ (∀ x,0 ≤ f x) ∧
      (∀ x,x ∉ D → f x=0) ∧ ∃ hf : MemLp f 2 volume,
      (∫ x,f x^2)=1 ∧ ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) < η*(c+ε) := by
  obtain ⟨F,hF,hFn,hFe⟩ := simultaneous_coordinate_energy hB hη hε
  let f := nonnegRepresentative D hD F
  have hf := nonnegRepresentative_memLp D hD F hF
  refine ⟨f,nonnegRepresentative_measurable D hD F,nonnegRepresentative_nonneg D hD F,
    fun x hx => nonnegRepresentative_zero D hD F hx,hf,?_,?_⟩
  · rw [nonnegRepresentative_square D hD F hF,hFn,one_pow]
  · intro i
    let ηn : ℝ≥0 := ⟨η,hη.le⟩
    have hh := norm_representative_diagonal_energy_le (Pi.single i (2*ηn)) F f hf
      (nonnegRepresentative_ae D hD F hF)
    rw [symbol_single i ηn] at hh
    exact hh.trans_lt (hFe i)

lemma real_coordinate_distance {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 volume)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/4) (hε : ε ≤ 1/10000)
    (hEn : ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) ≤ η*((1/10000)+ε))
    (j : ι) {r t : ℝ} (hr : r ∈ Ioo (-(5/2:ℝ)) (5/2)) (ht : t ∈ Ioo (-(5/2:ℝ)) (5/2)) :
    realDistance f ((r-t) • EuclideanSpace.single j 1) ≤ 3/500 := by
  rw [realDistance_eq f hf]
  have hh := directional_translate_bound (EuclideanSpace.single j (1:ℝ)) (r-t) η hη (complexLp f hf)
  rw [directionalSymbol_single] at hh
  have hnn : 0 ≤ ((r-t)^2+4*η)/η := div_nonneg (by positivity) hη.le
  have he := mul_le_mul_of_nonneg_left (hEn j) hnn
  have heq : (((r-t)^2+4*η)/η)*(η*((1/10000)+ε)) = ((r-t)^2+4*η)*((1/10000)+ε) := by
    field_simp
  rw [heq] at he
  apply hh.trans (he.trans ?_)
  have hd : (r-t)^2 ≤ 25 := by
    have hx : -(5:ℝ) ≤ r-t ∧ r-t ≤ 5 := by constructor <;> linarith [hr.1,hr.2,ht.1,ht.2]
    nlinarith [sq_nonneg (r-t+5),sq_nonneg (r-t-5)]
  have hA : (r-t)^2+4*η ≤ 26 := by linarith
  have hB : (1/10000:ℝ)+ε ≤ 1/5000 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (r-t)^2+4*η)
  nlinarith

omit [DecidableEq ι] in
lemma energy_weighted_density {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 volume)
    {η c t : ℝ} (hη : 0 < η) (v : ι → ℝ≥0) (ht : 0 ≤ t)
    (hηt : ∀ i,η ≤ t*(v i:ℝ)/2)
    (hE : ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) ≤ η*c) :
    energy (fun ξ => t*GaussianKernel.symbol v ξ) (complexLp f hf) ≤ (t*c/2)*∑ i,(v i:ℝ) := by
  classical
  apply (energy_weighted_le v hη hηt _).trans
  calc
    (∑ i,t*(v i:ℝ)/(2*η)*energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf)) ≤
        ∑ i,t*(v i:ℝ)/(2*η)*(η*c) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hE i) (by positivity)
    _ = (t*c/2)*∑ i,(v i:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp

omit [DecidableEq ι] in
lemma exists_coordinate_time (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) {t : ℝ} (ht : 0 < t) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1/4 ∧ ∀ i,η ≤ t*(v i:ℝ)/2 := by
  have hh : ∀ s : Finset ι,∃ η : ℝ,0 < η ∧ η ≤ 1/4 ∧ ∀ i ∈ s,η ≤ t*(v i:ℝ)/2 := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨1/4,by norm_num,le_rfl,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨η,hη,hη1,hηs⟩ := ih
      have hvi : (0:ℝ) < v i := hv i
      refine ⟨min η (t*(v i:ℝ)/2),lt_min hη (by positivity),
        (min_le_left _ _).trans hη1,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hηs j hj)
  obtain ⟨η,hη,hη1,hηs⟩ := hh Finset.univ
  exact ⟨η,hη,hη1,fun i => hηs i (Finset.mem_univ i)⟩

end HeatL2.Diagonal

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.LiftedRearrangement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lifted fiber rearrangement and overlap estimates. -/

section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Lift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma shear_preserving (e : E) : MeasurePreserving (shear e)
    ((volume : Measure E).prod volume) (volume.prod volume) := by
  have hp : MeasurePreserving (fun p : ℝ × E => (p.1,p.2+p.1 • e))
      ((volume : Measure ℝ).prod (volume : Measure E)) (volume.prod volume) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun s y => y+s • e) (by fun_prop)
    exact ae_of_all _ fun s => (measurePreserving_add_right volume (s • e)).map_eq
  exact (measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure E))).comp
    (hp.comp (measurePreserving_swap (μ := (volume : Measure E)) (ν := (volume : Measure ℝ))))

lemma lift_measurable (ell c : ℝ) (e : E) {f : E → ℝ} (hf : Measurable f) :
    Measurable (liftFunction ell c e f) := by
  have he : liftFunction ell c e f =
      ((Prod.snd ⁻¹' Ioo (-ell) ell) : Set (E × ℝ)).indicator (fun p => c*f (p.1+p.2 • e)) := by
    funext p
    by_cases hp : p.2 ∈ Ioo (-ell) ell <;> simp [liftFunction,indicator,hp]
  rw [he]
  exact (measurable_const.mul (hf.comp (by fun_prop))).indicator (measurable_snd measurableSet_Ioo)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_strip (ell c : ℝ) (e : E) (f : E → ℝ) (p : E × ℝ)
    (hp : ell ≤ |p.2|) : liftFunction ell c e f p = 0 := by
  apply indicator_of_notMem
  intro hh
  exact not_lt_of_ge hp (abs_lt.mpr hh)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_nonneg (ell : ℝ) {c : ℝ} (hc : 0 ≤ c) (e : E) {f : E → ℝ}
    (hf : ∀ x,0 ≤ f x) (p : E × ℝ) : 0 ≤ liftFunction ell c e f p :=
  indicator_nonneg (fun _ _ => mul_nonneg hc (hf _)) _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_square_eq (ell c : ℝ) (e : E) (f : E → ℝ) :
    (fun p => liftFunction ell c e f p^2) =
      (fun p : E × ℝ => (f p.1)^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2) ∘ shear e := by
  funext p
  change liftFunction ell c e f p^2 =
    f (p.1+p.2 • e)^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2
  by_cases hp : p.2 ∈ Ioo (-ell) ell
  · simp only [liftFunction,indicator_of_mem hp,mul_pow]
    ring
  · simp only [liftFunction,indicator_of_notMem hp,zero_pow (by norm_num : 2 ≠ 0),mul_zero]

lemma lift_memLp (ell c : ℝ) (e : E) {f : E → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 volume) : MemLp (liftFunction ell c e f) 2 (volume.prod volume) := by
  apply (memLp_two_iff_integrable_sq (lift_measurable ell c e hm).aestronglyMeasurable).mpr
  rw [lift_square_eq]
  apply (shear_preserving e).integrable_comp_of_integrable
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf).mul_prod
    ((integrableOn_const (s := Ioo (-ell) ell) (C := c^2) (hs := by simp)).integrable_indicator measurableSet_Ioo)

lemma lift_total_square {ell : ℝ} (hell : 0 ≤ ell) (c : ℝ) (e : E) (f : E → ℝ) :
    (∫ p, liftFunction ell c e f p^2 ∂(volume : Measure E).prod volume) =
      (2*ell)*c^2*(∫ x,f x^2) := by
  rw [lift_square_eq]
  change (∫ p, ((fun p : E × ℝ => (f p.1)^2 *
      (Ioo (-ell) ell).indicator (fun _ => c^2) p.2) ((shear e) p)) ∂volume.prod volume) = _
  rw [(shear_preserving e).integral_comp (shear e).measurableEmbedding
    (fun p : E × ℝ => f p.1^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2),
    integral_prod_mul (fun y : E => f y^2) ((Ioo (-ell) ell).indicator (fun _ => c^2)),
    integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul,
    Real.volume_real_Ioo_of_le (by linarith : -ell ≤ ell)]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_difference_eq (ell c : ℝ) (e a : E) (f : E → ℝ) (p : E × ℝ) :
    liftFunction ell c e f (p.1+a,p.2)-liftFunction ell c e f p =
      liftFunction ell c e (fun y => f (y+a)-f y) p := by
  by_cases hp : p.2 ∈ Ioo (-ell) ell
  · simp only [liftFunction,indicator_of_mem hp,show p.1+a+p.2 • e=p.1+p.2 • e+a by abel]
    ring
  · simp only [liftFunction,indicator_of_notMem hp,sub_self]

lemma lift_total_difference {ell : ℝ} (hell : 0 ≤ ell) (c : ℝ) (e a : E) (f : E → ℝ) :
    (∫ p, (liftFunction ell c e f (p.1+a,p.2)-liftFunction ell c e f p)^2
      ∂(volume : Measure E).prod volume) = (2*ell)*c^2*HeatL2.realDistance f a := by
  simp_rw [lift_difference_eq]
  exact lift_total_square hell c e _

end Lift
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section Lifting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fiberStar_horizontal_difference {ell c : ℝ} (hell : 0 ≤ ell) (hc : 0 ≤ c)
    (e a : E) {f : E → ℝ} (hm : Measurable f) (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) :
    (∫ p, ((fiberStar (liftFunction ell c e f) (p.1+a,p.2)).toReal-
      (fiberStar (liftFunction ell c e f) p).toReal)^2 ∂(volume : Measure E).prod volume) ≤
       (2*ell)*c^2*HeatL2.realDistance f a := by
  let F := liftFunction ell c e f
  let G := liftFunction ell c e (fun y => f (y+a))
  have hshift : ∀ p : E × ℝ,G p=F (p.1+a,p.2) := by
    intro p
    dsimp [G,F,liftFunction]
    congr 2
    funext s
    congr 2
    abel
  have hg : Measurable (fun y : E => f (y+a)) := hm.comp (by fun_prop)
  have hgLp : MemLp (fun y : E => f (y+a)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume a)
  have hh := fiberStar_total_difference (μ := (volume : Measure E))
    (lift_measurable ell c e hg) (lift_measurable ell c e hm)
    (lift_nonneg ell hc e (fun y => hfn (y+a))) (lift_nonneg ell hc e hfn)
    (superlevel_measure_ne_top_of_strip (lift_strip ell c e _))
    (superlevel_measure_ne_top_of_strip (lift_strip ell c e f))
    (lift_memLp ell c e hg hgLp) (lift_memLp ell c e hm hf)
  change (∫ p,((fiberStar G p).toReal-(fiberStar F p).toReal)^2 ∂volume.prod volume) ≤ (∫ p,(G p-F p)^2 ∂volume.prod volume) at hh
  have hstar : ∀ p : E × ℝ,fiberStar G p=fiberStar F (p.1+a,p.2) := by
    intro p
    unfold fiberStar
    congr 2
    funext s
    exact hshift (p.1,s)
  simp_rw [hstar,hshift] at hh
  exact hh.trans_eq (lift_total_difference hell c e a f)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lifted_star_supported {K : Set E} (hK : Convex ℝ K) {f : E → ℝ}
    (hf : ∀ y,y ∉ K → f y=0) (ell c : ℝ) (e : E)
    {p : E × ℝ} (hp : p.1 ∉ ShiftedSections.sectionDomain K e ell |p.2|) :
    fiberStar (liftFunction ell c e f) p=0 := by
  apply ShiftedSections.fiberStar_supported hK _ hp
  intro q hq
  rcases hq with hq | hq
  · by_cases hs : q.2 ∈ Ioo (-ell) ell
    · simp only [liftFunction,indicator_of_mem hs,hf _ hq,mul_zero]
    · exact indicator_of_notMem hs _
  · exact lift_strip ell c e f q hq

end Lifting
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section Height
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

lemma fiberStar_total_height {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) :
    (∫⁻ p,ENNReal.ofReal |p.2| *(fiberStar F p)^2 ∂μ.prod volume) =
      (∫⁻ r,∫⁻ t,∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ)/4 := by
  have hm : Measurable (fun p : X × ℝ => ENNReal.ofReal |p.2| * (fiberStar F p)^2) :=
    measurable_snd.abs.ennreal_ofReal.mul ((fiberStar_measurable hF).pow_const 2)
  rw [lintegral_prod _ hm.aemeasurable]
  have hp x := function_rearranged_height volume
    (show Measurable (fun s => F (x,s)) from hF.comp measurable_prodMk_left) (hfF x)
  change (∫⁻ x, (∫⁻ s,ENNReal.ofReal |s| * (fiberStar F (x,s))^2) ∂μ) = _
  simp_rw [show ∀ x, (∫⁻ s, ENNReal.ofReal |s| *(fiberStar F (x,s))^2) =
    (∫⁻ r,∫⁻ t, (ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2)/4 from hp,
    div_eq_mul_inv]
  rw [lintegral_mul_const' (4:ℝ≥0∞)⁻¹ _ (by norm_num)]
  congr 1
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro r
    apply lintegral_lintegral_swap
    exact (((hF.comp (measurable_fst.prodMk measurable_const)).min
      (hF.comp (measurable_fst.prodMk measurable_snd))).ennreal_ofReal.pow_const 2).aemeasurable
  · apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    exact (((hF.comp (measurable_fst.fst.prodMk measurable_fst.snd)).min
      (hF.comp (measurable_fst.fst.prodMk measurable_snd))).ennreal_ofReal.pow_const 2)

omit [MeasurableSpace X] in
lemma fiberStar_strip {F : X × ℝ → ℝ} {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) {p : X × ℝ} (hp : ell ≤ |p.2|) :
    fiberStar F p=0 := by
  apply fiberStar_eq_zero_of_measure_le
  intro u
  calc
    volume (superlevel (fun r => F (p.1,r)) u) ≤ volume (Ioo (-ell) ell) := by
      apply measure_mono
      intro s hs
      change 0 < u ∧ u < F (p.1,s) at hs
      apply abs_lt.mp
      by_contra hn
      rw [hstrip (p.1,s) (not_lt.mp hn)] at hs
      linarith [hs.1,hs.2]
    _ = ENNReal.ofReal (2*ell) := by rw [Real.volume_Ioo]; congr 1; ring
    _ ≤ ENNReal.ofReal (2*|p.2|) := ENNReal.ofReal_le_ofReal (by linarith)

omit [SFinite μ] in
lemma fiberStar_height_integrable {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfn : ∀ p,0 ≤ F p) (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) :
    Integrable (fun p => |p.2| *(fiberStar F p).toReal^2) (μ.prod volume) := by
  have hh := fiberStar_memLp hF hfn hfF hiF
  have hi := ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mp hh).const_mul ell
  apply hi.mono' ((measurable_snd.abs.mul ((fiberStar_measurable hF).ennreal_toReal.pow_const 2)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    by_cases hp : ell ≤ |p.2|
    · have hz : fiberStar F p = 0 := fiberStar_strip hstrip hp
      simp only [Pi.mul_apply,hz,ENNReal.toReal_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right (not_le.mp hp).le (sq_nonneg _)

lemma fiberStar_total_height_lower {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    {ell m : ℝ} (hell : 0 ≤ ell) (hm : 0 ≤ m)
    (hbound : ∀ r ∈ Ioo (-ell) ell, ∀ t ∈ Ioo (-ell) ell,
      ENNReal.ofReal m ≤ ∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ) :
    ENNReal.ofReal (ell^2*m) ≤
      ∫⁻ p,ENNReal.ofReal |p.2| * (fiberStar F p)^2 ∂μ.prod volume := by
  rw [fiberStar_total_height hF hfF]
  let I := Ioo (-ell) ell
  let G := fun r t => ∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ
  have hinner r (hr : r ∈ I) : ENNReal.ofReal m * volume I ≤ ∫⁻ t,G r t := by
    calc
      _ = ∫⁻ t in I,ENNReal.ofReal m := by simp
      _ ≤ ∫⁻ t in I,G r t := setLIntegral_mono' measurableSet_Ioo (hbound r hr)
      _ ≤ ∫⁻ t,G r t := setLIntegral_le_lintegral _ _
  have htotal : ENNReal.ofReal m * volume I * volume I ≤ ∫⁻ r,∫⁻ t,G r t := by
    calc
      _ = ∫⁻ r in I,ENNReal.ofReal m * volume I := by simp
      _ ≤ ∫⁻ r in I,∫⁻ t,G r t := setLIntegral_mono' measurableSet_Ioo hinner
      _ ≤ ∫⁻ r,∫⁻ t,G r t := setLIntegral_le_lintegral _ _
  have hvol : volume I = ENNReal.ofReal (2*ell) := by
    dsimp [I]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have he : ENNReal.ofReal (ell^2*m) =
      (ENNReal.ofReal m * volume I * volume I)/4 := by
    rw [hvol,← ENNReal.ofReal_mul hm,
      ← ENNReal.ofReal_mul (mul_nonneg hm (by positivity)),
      show (4:ℝ≥0∞)=ENNReal.ofReal (4:ℝ) by norm_num,← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    congr 1
    ring
  rw [he]
  exact ENNReal.div_le_div_right htotal 4

omit [SFinite μ] in
lemma fiberStar_total_real_height {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfn : ∀ p,0 ≤ F p) (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) :
    ENNReal.ofReal (∫ p,|p.2| * (fiberStar F p).toReal^2 ∂μ.prod volume) =
      ∫⁻ p,ENNReal.ofReal |p.2| * (fiberStar F p)^2 ∂μ.prod volume := by
  rw [ofReal_integral_eq_lintegral_ofReal (fiberStar_height_integrable hF hfn hfF hiF hstrip)
    (ae_of_all _ fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  have hi : (∫⁻ p,(fiberStar F p)^2 ∂μ.prod volume) ≠ ⊤ := by
    rw [fiberStar_total_square hF hfF]
    exact ofReal_square_integral_ne_top hiF hfn
  apply lintegral_congr_ae
  filter_upwards [ae_finite_of_square (fiberStar_measurable hF) hi] with p hp
  rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hp.ne]

end Height
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
namespace VerticalRearrangement
section Overlap
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma min_square_lower (u v : ℝ) :
    (9/10:ℝ)*u^2-10*(u-v)^2 ≤ (min u v)^2 := by
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    nlinarith [sq_nonneg u,sq_nonneg (u-v)]
  · rw [min_eq_right h]
    nlinarith [sq_nonneg (u-10*(u-v)),sq_nonneg (u-v)]

lemma min_square_integrable {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x,0 ≤ f x) (hgn : ∀ x,0 ≤ g x) :
    Integrable (fun x => (min (f x) (g x))^2) μ := by
  apply ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf).mono'
    ((hf.aestronglyMeasurable.aemeasurable.min hg.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_min (hfn x) (hgn x)) (min_le_left _ _) _

lemma min_square_integral_lower {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x,0 ≤ f x) (hgn : ∀ x,0 ≤ g x) :
    (9/10:ℝ)*(∫ x,f x^2 ∂μ)-10*(∫ x,(f x-g x)^2 ∂μ) ≤
      ∫ x,(min (f x) (g x))^2 ∂μ := by
  have hf2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hd2 := (memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  simp only [Pi.sub_apply] at hd2
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hf2.const_mul _) (hd2.const_mul _)]
  exact integral_mono (hf2.const_mul _ |>.sub (hd2.const_mul _))
    (min_square_integrable hf hg hfn hgn) (fun x => min_square_lower (f x) (g x))

end Overlap
section Translate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma translate_pair_square (f : E → ℝ) (a b : E) :
    (∫ y,(f (y+a)-f (y+b))^2) = HeatL2.realDistance f (a-b) := by
  have hh := (measurePreserving_add_right volume b).integral_comp
    (Homeomorph.addRight b).measurableEmbedding (fun y => (f (y+(a-b))-f y)^2)
  simpa only [HeatL2.realDistance,show ∀ y:E,y+b+(a-b)=y+a by intro y; abel] using hh

lemma translate_min_square_lower {f : E → ℝ} (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) (hn : (∫ x,f x^2)=1) (a b : E)
    (hd : HeatL2.realDistance f (a-b) ≤ 3/500) :
    (21/25:ℝ) ≤ ∫ y,(min (f (y+a)) (f (y+b)))^2 := by
  have hh := min_square_integral_lower
    (hf.comp_measurePreserving (measurePreserving_add_right volume a))
    (hf.comp_measurePreserving (measurePreserving_add_right volume b))
    (fun y => hfn (y+a)) (fun y => hfn (y+b))
  simp only [Function.comp_apply] at hh
  rw [(measurePreserving_add_right volume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding (fun y => f y^2),
    translate_pair_square,hn] at hh
  linarith

end Translate
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section LiftHeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_min_square {ell c r t : ℝ} (hc : 0 ≤ c) (e : E) (f : E → ℝ)
    (hr : r ∈ Ioo (-ell) ell) (ht : t ∈ Ioo (-ell) ell) :
    (fun y => (min (liftFunction ell c e f (y,r)) (liftFunction ell c e f (y,t)))^2) =
      fun y => c^2 * (min (f (y+r • e)) (f (y+t • e)))^2 := by
  ext y
  simp only [liftFunction,indicator_of_mem hr,indicator_of_mem ht,← mul_min_of_nonneg _ _ hc,mul_pow]

lemma lift_height_lower {f : E → ℝ} (hm : Measurable f) (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) (hn : (∫ x,f x^2)=1) (e : E)
    (hd : ∀ r ∈ Ioo (-(5/2:ℝ)) (5/2),∀ t ∈ Ioo (-(5/2:ℝ)) (5/2),
      HeatL2.realDistance f ((r-t) • e) ≤ 3/500) :
    (21/20:ℝ) ≤ ∫ p,|p.2| * (fiberStar (liftFunction (5/2) (Real.sqrt (1/5)) e f) p).toReal^2
      ∂(volume : Measure E).prod volume := by
  let c := Real.sqrt (1/5:ℝ)
  let F := liftFunction (5/2) c e f
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2=(1/5:ℝ) := Real.sq_sqrt (by norm_num)
  have hFm : Measurable F := lift_measurable _ _ _ hm
  have hFn : ∀ p,0 ≤ F p := lift_nonneg _ hc _ hfn
  have hFi : MemLp F 2 (volume.prod volume) := lift_memLp _ _ _ hm hf
  have hFs := lift_strip (5/2:ℝ) c e f
  have hFfin := superlevel_measure_ne_top_of_strip hFs
  have hbound : ∀ r ∈ Ioo (-(5/2:ℝ)) (5/2),∀ t ∈ Ioo (-(5/2:ℝ)) (5/2),
      ENNReal.ofReal (c^2*(21/25:ℝ)) ≤
        ∫⁻ y,(ENNReal.ofReal (min (F (y,r)) (F (y,t))))^2 := by
    intro r hr t ht
    have hmin := translate_min_square_lower hf hfn hn (r • e) (t • e)
      (by simpa only [← sub_smul] using hd r hr t ht)
    have hmini := min_square_integrable
      (hf.comp_measurePreserving (measurePreserving_add_right volume (r • e)))
      (hf.comp_measurePreserving (measurePreserving_add_right volume (t • e)))
      (fun y => hfn (y+r • e)) (fun y => hfn (y+t • e))
    have hei := ofReal_integral_eq_lintegral_ofReal (hmini.const_mul (c^2))
      (ae_of_all _ fun y => mul_nonneg (sq_nonneg c) (sq_nonneg _))
    have he : (fun y => (min (F (y,r)) (F (y,t)))^2) =
        fun y => c^2*(min (f (y+r • e)) (f (y+t • e)))^2 := lift_min_square hc e f hr ht
    calc
      ENNReal.ofReal (c^2*(21/25:ℝ)) ≤ ENNReal.ofReal (c^2*(∫ y,(min (f (y+r • e)) (f (y+t • e)))^2)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmin (sq_nonneg c))
      _ = ∫⁻ y,ENNReal.ofReal (c^2*(min (f (y+r • e)) (f (y+t • e)))^2) := by
        rw [← integral_const_mul]
        exact hei
      _ = ∫⁻ y,(ENNReal.ofReal (min (F (y,r)) (F (y,t))))^2 := by
        apply lintegral_congr
        intro y
        rw [← congrFun he y]
        exact ENNReal.ofReal_pow (le_min (hFn _) (hFn _)) _
  have hH := fiberStar_total_height_lower hFm hFfin (by norm_num : (0:ℝ)≤5/2)
    (by positivity : 0 ≤ c^2*(21/25:ℝ)) hbound
  rw [hc2] at hH
  norm_num at hH
  rw [← fiberStar_total_real_height hFm hFn hFfin hFi hFs] at hH
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)))).mp hH

end LiftHeight
end VerticalRearrangement

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
open VerticalRearrangement HeatL2 HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lifted_test {K : Set (EuclideanSpace ℝ ι)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hB : Bound K hKm (1/10000)) (j : ι) {η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1/4) (hε : 0 < ε) (hε1 : ε ≤ 1/10000) :
    ∃ f : EuclideanSpace ℝ ι → ℝ, ∃ hf : MemLp f 2 volume,
      (∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) < η*((1/10000)+ε)) ∧
      ∃ G : EuclideanSpace ℝ ι × ℝ → ℝ,
      Measurable G ∧ MemLp G 2 (volume.prod volume) ∧
      (∀ p,p.1 ∉ sectionDomain K (EuclideanSpace.single j 1) (5/2) |p.2| → G p=0) ∧
      (∫ p,G p^2 ∂volume.prod volume)=1 ∧
      Integrable (fun p => |p.2| *G p^2) (volume.prod volume) ∧
      (21/20:ℝ) ≤ ∫ p,|p.2| *G p^2 ∂volume.prod volume ∧
      ∀ a,(∫ p,(G (p.1+a,p.2)-G p)^2 ∂volume.prod volume) ≤ realDistance f a := by
  obtain ⟨f,hm,hfn,hfs,hf,hn,hE⟩ := simultaneous_real_density hB hη hε
  let e := EuclideanSpace.single j (1:ℝ)
  let c := Real.sqrt (1/5:ℝ)
  let F := liftFunction (5/2) c e f
  let G := fun p => (fiberStar F p).toReal
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2=(1/5:ℝ) := Real.sq_sqrt (by norm_num)
  have hFm : Measurable F := lift_measurable _ _ _ hm
  have hFn : ∀ p,0 ≤ F p := lift_nonneg _ hc _ hfn
  have hFi : MemLp F 2 (volume.prod volume) := lift_memLp _ _ _ hm hf
  have hFs := lift_strip (5/2:ℝ) c e f
  have hFfin := superlevel_measure_ne_top_of_strip hFs
  have hGn : (∫ p,G p^2 ∂volume.prod volume)=1 := by
    rw [fiberStar_total_real_square hFm hFn hFfin (ofReal_square_integral_ne_top hFi hFn),
      lift_total_square (by norm_num : (0:ℝ)≤5/2) c e f,hc2,hn]
    norm_num
  refine ⟨f,hf,hE,G,(fiberStar_measurable hFm).ennreal_toReal,
    fiberStar_memLp hFm hFn hFfin hFi,?_,hGn,?_,?_,?_⟩
  · intro p hp
    rw [show G p = (fiberStar (liftFunction (5/2) c e f) p).toReal from rfl,
      lifted_star_supported hKc hfs (5/2) c e hp,ENNReal.toReal_zero]
  · exact fiberStar_height_integrable hFm hFn hFfin hFi hFs
  · exact lift_height_lower hm hf hfn hn e (fun r hr t ht =>
      real_coordinate_distance hf hη hη1 hε1 (fun i => (hE i).le) j hr ht)
  · intro a
    have hh := fiberStar_horizontal_difference (by norm_num : (0:ℝ)≤5/2) hc e a hm hf hfn
    rw [hc2] at hh
    norm_num at hh
    exact hh

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Adaptive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy-preserving sections and adaptive coordinate selection. -/

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace ShiftedSections
open HeatL2 HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma section_crossing {K : Set (EuclideanSpace ℝ ι)} (hKm : MeasurableSet K)
    (hKc : Convex ℝ K) (hB : Bound K hKm (1/10000)) (j : ι) :
    ∃ r ∈ activeHeights K (EuclideanSpace.single j 1) (5/2),1 < r := by
  obtain ⟨f,hf,_,G,_,hG,hGs,hn,hH,hh,_⟩ := lifted_test hKm hKc hB j
    (η := 1/4) (ε := 1/10000) (by norm_num) le_rfl (by norm_num) le_rfl
  exact height_above_one _ _ hG hn hH (by linarith) hGs

omit [DecidableEq ι] in
lemma symbol_mul (t : ℝ≥0) (v : ι → ℝ≥0) :
    GaussianKernel.symbol (fun i => t*v i) = fun ξ => (t:ℝ)*GaussianKernel.symbol v ξ := by
  funext ξ
  simp only [GaussianKernel.symbol,NNReal.coe_mul]
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma section_rate_le {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι)
    (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) :
    sectionRate K hKo (EuclideanSpace.single j 1) (5/2) v 1 ≤
      ((1/10000:ℝ)/2)*∑ i,(v i:ℝ) := by
  let e := EuclideanSpace.single j (1:ℝ)
  let h := sectionRate K hKo e (5/2) v 1
  have hr := section_crossing hKo.measurableSet hKc hB j
  obtain ⟨h0,h1⟩ := activeHeights_contains_one hKc e (5/2) hr
  obtain ⟨a,ha,hline⟩ := EuclideanSteinitz.convex_supporting_line
    (sectionRate_convex hKo hKb hKc e (5/2) v (fun i => (hv i).ne'))
    (sectionRate_monotone hKo hKb hKc e (5/2) v) h0 h1 hr
  let L := h+a*(5/2)
  have hh : 0 ≤ h := sectionRate_nonneg hKo hKb e (5/2) v h1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1/10000 →
      h ≤ (1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ)) := by
    intro ε hε hε1
    obtain ⟨η,hη,hη1,hηt⟩ := exists_coordinate_time v hv hε
    obtain ⟨f,hf,hE,G,hGm,hG,hGs,hn,hH,hheight,hcon⟩ :=
      lifted_test hKo.measurableSet hKc hB j hη hη1 hε hε1
    let εn : ℝ≥0 := ⟨ε,hε.le⟩
    let A := GaussianKernel.scaleMap (fun i => εn*v i)
    have hA : gaussianSymbol A = fun ξ => ε*GaussianKernel.symbol v ξ := by
      rw [GaussianKernel.symbol_eq,symbol_mul]
      rfl
    have hlow := integrated_section_rate hKo hKb e (by norm_num : (0:ℝ) ≤ 5/2)
      v hh ha hline hε (by linarith) A hA hGm hG hGs hn hH (by linarith)
    have hupp := integral_sliceEnergy_le hG hf A hcon
    rw [hA] at hupp
    have hweight := energy_weighted_density hf hη v hε.le hηt (fun i => (hE i).le)
    have hboth := hlow.trans (hupp.trans hweight)
    change ε/(1+ε*L)*h ≤ ε*((1/10000)+ε)/2*(∑ i,(v i:ℝ)) at hboth
    have hd : 0 < 1+ε*L := by positivity
    have hc : 0 < ε/(1+ε*L) := by positivity
    apply (mul_le_mul_iff_of_pos_left hc).mp
    calc
      ε/(1+ε*L)*h ≤ ε*((1/10000)+ε)/2*(∑ i,(v i:ℝ)) := hboth
      _ = ε/(1+ε*L)*((1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ))) := by field_simp
  have hcont : Continuous (fun ε : ℝ => (1+ε*L)*(((1/10000)+ε)/2)*(∑ i,(v i:ℝ))) := by fun_prop
  apply ge_of_tendsto ((hcont.tendsto' 0 _ (by ring)).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1/10000 by norm_num)] with ε hε
  exact hstep ε hε.1 hε.2.le

lemma section_bound_positive {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι)
    (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) :
    Real.exp (-((1/10000:ℝ)/2)*∑ i,(v i:ℝ)) ≤
      sectionNorm K hKo (EuclideanSpace.single j 1) (5/2) 1 v := by
  have h1 := (activeHeights_contains_one hKc _ _ (section_crossing hKo.measurableSet hKc hB j)).2
  have hp := sectionNorm_pos hKo hKb (EuclideanSpace.single j 1) (5/2) v h1
  have hh := section_rate_le hKo hKb hKc hB j v hv
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  change -Real.log (sectionNorm K hKo (EuclideanSpace.single j 1) (5/2) 1 v) ≤ _ at hh
  linarith

lemma section_bound {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K)
    (hB : Bound K hKo.measurableSet (1/10000)) (j : ι) :
    Bound (sectionDomain K (EuclideanSpace.single j 1) (5/2) 1)
      (section_open hKo _ _ _).measurableSet (1/10000) := by
  intro v
  let e := EuclideanSpace.single j (1:ℝ)
  let D := sectionDomain K e (5/2) 1
  have hstep : ∀ δ : ℝ,0 < δ →
      Real.exp (-((1/10000:ℝ)/2)*(∑ i,((v i:ℝ)+δ))) ≤
        sectionNorm K hKo e (5/2) 1 v := by
    intro δ hδ
    let w : ι → ℝ≥0 := fun i => v i+⟨δ,hδ.le⟩
    have hw : ∀ i,0 < w i := by intro i; change 0 < (v i:ℝ)+δ; positivity
    have hb := section_bound_positive hKo hKb hKc hB j w hw
    have hm : ∀ ξ,GaussianKernel.symbol v ξ ≤ GaussianKernel.symbol w ξ := by
      intro ξ
      unfold GaussianKernel.symbol
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      change (v i:ℝ) ≤ (v i:ℝ)+δ
      linarith
    exact hb.trans (compressed_norm_mono_symbol D (section_open hKo e (5/2) 1).measurableSet
      _ _ (GaussianKernel.symbol_continuous v).aestronglyMeasurable
      (GaussianKernel.symbol_continuous w).aestronglyMeasurable
      (GaussianKernel.symbol_nonneg v) (GaussianKernel.symbol_nonneg w) hm)
  have hc : Continuous (fun δ : ℝ => Real.exp (-((1/10000:ℝ)/2)*(∑ i,((v i:ℝ)+δ)))) := by fun_prop
  apply le_of_tendsto ((hc.tendsto' 0 _ (by simp)).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hstep δ hδ

end ShiftedSections

end

section

open MeasureTheory Set
namespace ShiftedSections
open HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Good.zero_mem {K : Set (Coeff (ι := ι))} (hK : Good K) : (0:Coeff) ∈ K :=
  zero_mem_of_symmetric_convex hK.convex hK.symmetric hK.nonempty

lemma Good.section {K : Set (Coeff (ι := ι))} (hK : Good K) (j : ι) :
    Good (sectionDomain K (EuclideanSpace.single j 1) (5/2) 1) := by
  refine ⟨?_,section_open hK.isOpen _ _ _,section_bounded hK.bounded _ (by norm_num),
    section_convex hK.convex _ _ _,section_symmetric hK.symmetric _ _ _,
    section_bound hK.isOpen hK.bounded hK.convex hK.bound j⟩
  exact (activeHeights_contains_one hK.convex _ _
    (section_crossing hK.isOpen.measurableSet hK.convex hK.bound j)).2.2

lemma backward_good {n : ℕ} (j : Fin n → ι) {K : Set (Coeff (ι := ι))} (hK : Good K) :
    Good (backward j K) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact (ih (fun i => j i.succ)).section (j 0)

lemma exists_walk {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (hq : ∀ i x,|q i x| ≤ 1/4) {K : Set (Coeff (ι := ι))} (hK : Good K)
    {x : Coeff (ι := ι)} (hx : x ∈ backward j K) :
    ∃ ε : Fin n → ℝ,(∀ i,ε i = -1 ∨ ε i=1) ∧ walk j q ε x ∈ K := by
  induction n generalizing x with
  | zero => exact ⟨Fin.elim0,fun i => i.elim0,hx⟩
  | succ n ih =>
    have htail := backward_good (fun i : Fin n => j i.succ) hK
    obtain ⟨e,he,hxe⟩ := shifted_step htail.convex (EuclideanSpace.single (j 0) 1) hx (hq 0 x)
    obtain ⟨ε,hε,hend⟩ := ih (fun i => j i.succ) (fun i => q i.succ)
      (fun i x => hq i.succ x) hxe
    refine ⟨Fin.cons e ε,?_,?_⟩
    · intro i
      refine Fin.cases he (fun i => ?_) i
      exact hε i
    · simpa only [walk,Fin.cons_zero,Fin.cons_succ] using hend

lemma adaptive_signs {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (hq : ∀ i x,|q i x| ≤ 1/4) {K : Set (Coeff (ι := ι))} (hK : Good K) :
    ∃ ε : Fin n → ℝ,(∀ i,ε i = -1 ∨ ε i=1) ∧ walk j q ε 0 ∈ K :=
  exists_walk j q hq hK (backward_good j hK).zero_mem

end ShiftedSections

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.SigningData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized predictors and backward-forward shifted walks. -/

section

open MeasureTheory Set
namespace ShiftedSections
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma clip_bound (u : ℝ) : |clip u|≤1/4 := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩
lemma clip_eq {u : ℝ} (hu : |u|<1/4) : clip u=u := by
  obtain ⟨hl,hr⟩ := abs_lt.mp hu
  rw [clip,min_eq_left hr.le,max_eq_right hl.le]

omit [Fintype ι] in
lemma walk_linear_invariant {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) (f : Coeff (ι := ι) →L[ℝ] ℝ)
    (hf : ∀ i,f (EuclideanSpace.single (j i) 1)=0) : f (walk j q ε x)=f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [walk,ih (fun i => j i.succ) (fun i => q i.succ) (fun i => ε i.succ) _ (fun i => hf i.succ)]
    simp only [map_add,map_smul,hf 0,smul_zero,add_zero]

omit [Fintype ι] in
lemma walk_coordinate_outside {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) (k : ι) (hk : ∀ i,k≠j i) :
    (walk j q ε x) k=x k := by
  exact walk_linear_invariant j q ε x (EuclideanSpace.proj k) (by intro i; simp [hk i])

omit [Fintype ι] in
lemma walk_coordinate_equations {n : ℕ} (j : Fin n → ι) (hj : Function.Injective j)
    (m : Fin n → Coeff (ι := ι) →L[ℝ] ℝ)
    (hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (j l) 1)=0)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) :
    ∀ i,(walk j (fun i y => clip (m i y)) ε x) (j i)=x (j i)+clip (m i (walk j (fun i y => clip (m i y)) ε x))+ε i := by
  induction n generalizing x with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    let jt := fun i : Fin n => j i.succ
    let mt := fun i : Fin n => m i.succ
    let et := fun i : Fin n => ε i.succ
    let x' := x+(clip (m 0 x)+ε 0) • EuclideanSpace.single (j 0) 1
    have htail : Function.Injective jt := fun i l h => Fin.succ_injective n (hj h)
    have hmt : ∀ i l : Fin n,i≤l → mt i (EuclideanSpace.single (jt l) 1)=0 :=
      fun i l h => hm i.succ l.succ (Fin.succ_le_succ_iff.mpr h)
    have hx0 : ∀ i : Fin n,j 0≠jt i := by
      intro i he
      exact Fin.succ_ne_zero i (hj he).symm
    have hout := walk_coordinate_outside jt (fun i y => clip (mt i y)) et x' (j 0) hx0
    have hinv := walk_linear_invariant jt (fun i y => clip (mt i y)) et x' (m 0)
      (fun i => hm 0 i.succ (Fin.zero_le _))
    have hzero : m 0 x'=m 0 x := by
      simp only [x',map_add,map_smul,hm 0 0 le_rfl,smul_zero,add_zero]
    have hrec := ih jt htail mt hmt et x'
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change (walk jt (fun i y => clip (mt i y)) et x') (j 0) = _
      rw [hout]
      change x' (j 0)=x (j 0)+clip (m 0 (walk jt (fun i y => clip (mt i y)) et x'))+ε 0
      rw [hinv,hzero]
      simp only [x',PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
      ring
    · change (walk jt (fun i y => clip (mt i y)) et x') (jt i)= _
      rw [hrec i]
      have he : x' (jt i)=x (j i.succ) := by
        simp only [x',PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_eq_right (Ne.symm (hx0 i)),smul_eq_mul,mul_zero,add_zero]
        rfl
      rw [he]
      rfl

lemma adaptive_linear_equations_oai {n : ℕ} (j : Fin n → ι) (hj : Function.Injective j)
    (m : Fin n → Coeff (ι := ι) →L[ℝ] ℝ)
    (hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (j l) 1)=0)
    {K : Set (Coeff (ι := ι))} (hK : Good K) (hslab : ∀ x∈K,∀ i,|m i x|<1/4) :
    ∃ ε : Fin n → ℝ,∃ x : Coeff (ι := ι),
      (∀ i,ε i = -1 ∨ ε i=1) ∧ x∈K ∧
      (∀ k,(∀ i,k≠j i) → x k=0) ∧ (∀ i,x (j i)=m i x+ε i) := by
  obtain ⟨ε,hε,hx⟩ := adaptive_signs j (fun i y => clip (m i y)) (fun i y => clip_bound _) hK
  let x := walk j (fun i y => clip (m i y)) ε 0
  refine ⟨ε,x,hε,hx,?_,?_⟩
  · intro k hk
    exact walk_coordinate_outside j (fun i y => clip (m i y)) ε 0 k hk
  · intro i
    have hh := walk_coordinate_equations j hj m hm ε 0 i
    change x (j i)=(0:Coeff) (j i)+clip (m i x)+ε i at hh
    simpa only [PiLp.zero_apply,zero_add,clip_eq (hslab x hx i)] using hh

end ShiftedSections

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ShiftedSections.adaptive_linear_equations_oai.{u_1} := @OAI.ShiftedSections.adaptive_linear_equations_oai.{u_1}
