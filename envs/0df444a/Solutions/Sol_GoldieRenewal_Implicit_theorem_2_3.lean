-- Prove2me | solution 1 for GoldieRenewal.Implicit.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T02:30:07.708706+00:00
-- url     : https://prove2.me/submissions/ee47815c-d120-43af-9678-24aae1cbe579

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Definitions.Def_GoldieRenewal_Implicit_DRi
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures
import Theorems.Thm_GoldieRenewal_Implicit_key_renewal_limit
import Theorems.Thm_GoldieRenewal_Implicit_eq_9_12_9_13
import Theorems.Thm_GoldieRenewal_Implicit_lemma_9_3
import Theorems.Thm_GoldieRenewal_Implicit_lemma_2_2

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GoldieRenewal.Implicit.Red

/-- the smoothing kernel `k(s) = 1_{s ≥ 0} e^{-s}` -/
noncomputable def kern (s : ℝ) : ℝ := Set.indicator (Set.Ici 0) (fun s => Real.exp (-s)) s

lemma kern_integrable : Integrable kern := by
  unfold kern
  rw [integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa using integrableOn_exp_neg_Ioi 0

lemma kern_integral : ∫ s, kern s = 1 := by
  unfold kern
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact integral_exp_neg_Ioi_zero

lemma smooth_eq_conv (g : ℝ → ℝ) (t : ℝ) :
    smooth g t = (convolution g kern (ContinuousLinearMap.lsmul ℝ ℝ) volume) t := by
  rw [convolution_lsmul, smooth, ← integral_indicator measurableSet_Iic]
  congr 1
  funext u
  by_cases hu : u ≤ t
  · have h0 : (0:ℝ) ≤ t - u := by linarith
    simp [Set.indicator, kern, hu, h0, mul_comm]
  · have h0 : ¬ (0:ℝ) ≤ t - u := by linarith
    simp [Set.indicator, kern, hu, h0]

/-- (A2) `∫ ğ = ∫ g` for `g ∈ L¹`. -/
lemma integral_smooth (g : ℝ → ℝ) (hg : Integrable g) : ∫ t, smooth g t = ∫ t, g t := by
  have : (fun t => smooth g t) = (convolution g kern (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    funext (smooth_eq_conv g)
  rw [this, integral_convolution _ hg kern_integrable, kern_integral]
  simp

/-- (A1) `ř(log T) = T⁻¹ ∫₀^T u^κ P(R > u) du`. -/
lemma smooth_rFun_log {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ)
    (T : ℝ) (hT : 0 < T) :
    smooth (rFun P R κ) (Real.log T) =
      (∫ u in (0 : ℝ)..T, u ^ κ * P.real {ω | u < R ω}) / T := by
  rw [intervalIntegral.integral_of_le hT.le, ← integral_div]
  have himg : Real.exp '' Set.Iic (Real.log T) = Set.Ioc 0 T := by
    ext v
    simp only [Set.mem_image, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Real.exp_pos u, ?_⟩
      calc Real.exp u ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr hu
        _ = T := Real.exp_log hT
    · rintro ⟨hv, hvT⟩
      exact ⟨Real.log v, Real.log_le_log hv hvT, Real.exp_log hv⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  unfold smooth rFun
  refine setIntegral_congr_fun measurableSet_Iic (fun u _ => ?_)
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos u)]
  rw [← Real.exp_mul, Real.exp_neg, Real.exp_sub, Real.exp_log hT]
  have h1 : Real.exp (κ * u) = Real.exp (u * κ) := by rw [mul_comm]
  rw [h1]
  field_simp

/-- (A3) change of variables `t = e^u` in a tail integral. -/
lemma integrableOn_Ioi_iff_exp (h : ℝ → ℝ) :
    IntegrableOn h (Set.Ioi 0) ↔ Integrable (fun u => Real.exp u * h (Real.exp u)) := by
  have himg : Real.exp '' Set.univ = Set.Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ]
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos _)]

lemma integral_Ioi_eq_exp (h : ℝ → ℝ) :
    ∫ t in Set.Ioi 0, h t = ∫ u, Real.exp u * h (Real.exp u) := by
  have himg : Real.exp '' Set.univ = Set.Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos _)]

lemma exp_mul_tailDiffPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ)
    (κ : ℝ) (u : ℝ) :
    Real.exp u * tailDiffPlus P M R κ (Real.exp u) = gOne P M R κ u := by
  unfold tailDiffPlus gOne
  rw [← Real.exp_mul]
  have : Real.exp u * Real.exp (u * (κ - 1)) = Real.exp (κ * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

lemma gOne_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ)
    (h28 : TailCondPlus P M R κ) : Integrable (gOne P M R κ) := by
  have := (integrableOn_Ioi_iff_exp (tailDiffPlus P M R κ)).mp h28
  simpa only [exp_mul_tailDiffPlus] using this

lemma integral_gOne {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    ∫ u, gOne P M R κ u = ∫ t in Set.Ioi 0, tailDiffPlus P M R κ t := by
  rw [integral_Ioi_eq_exp]
  simp only [exp_mul_tailDiffPlus]

/-- **Case 1, right tail**, from the key renewal limit and the Tauberian Lemma 9.3. -/
theorem case1_plus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h28 : TailCondPlus P M R κ) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Cplus P M R κ)) := by
  have K := key_renewal_limit P M R hM hR κ hC hind hM_nonneg h28
  rw [integral_smooth _ (gOne_integrable P M R κ h28), integral_gOne] at K
  have K2 := K.comp Real.tendsto_log_atTop
  apply lemma_9_3 P R hR κ hC.pos
  refine K2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp]
  exact smooth_rFun_log P R κ T hT

lemma tailDiffPlus_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    tailDiffPlus P M (fun ω => -R ω) κ = tailDiffMinus P M R κ := by
  funext t
  unfold tailDiffPlus tailDiffMinus
  have h1 : {ω | t < -R ω} = {ω | R ω < -t} := by ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have h2 : {ω | t < M ω * -R ω} = {ω | M ω * R ω < -t} := by
    ext ω; simp only [Set.mem_ofPred_eq, mul_neg]; constructor <;> intro h <;> linarith
  rw [h1, h2]

/-- **Case 1, left tail**: Case 1 right tail for `-R`. -/
theorem case1_minus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h29 : TailCondMinus P M R κ) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Cminus P M R κ)) := by
  have hind' : IndepFun (fun ω => -R ω) M P := hind.comp measurable_neg measurable_id
  have h28 : TailCondPlus P M (fun ω => -R ω) κ := by
    unfold TailCondPlus; rw [tailDiffPlus_neg]; exact h29
  have := case1_plus P M (fun ω => -R ω) hM hR.neg κ hC hind' hM_nonneg h28
  have hC' : Cplus P M (fun ω => -R ω) κ = Cminus P M R κ := by
    unfold Cplus Cminus; rw [tailDiffPlus_neg]
  rw [hC'] at this
  refine this.congr (fun t => ?_)
  congr 2
  ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith

/-! ### Measure-level structure of `etaCase2`, `etaZero` -/

/-- unnormalised tilted law of `log|M|` on `{M ∈ s}`: `e^{κy} P(M ∈ s, log|M| ∈ dy)` -/
noncomputable def tiltOn (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) : Measure ℝ :=
  ((μ.restrict s).map (fun x => Real.log |x|)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (κ * u)))

lemma meas_logabs : Measurable (fun x : ℝ => Real.log |x|) :=
  Real.measurable_log.comp continuous_abs.measurable

lemma meas_expden (κ : ℝ) : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (κ * u))) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

instance tiltOn_sfinite (κ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (s : Set ℝ) :
    SFinite (tiltOn κ μ s) := by
  unfold tiltOn; infer_instance

lemma lintegral_tiltOn (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(tiltOn κ μ s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (κ * Real.log |x|)) * f (Real.log |x|) ∂μ := by
  unfold tiltOn
  rw [lintegral_withDensity_eq_lintegral_mul _ (meas_expden κ) hf,
    lintegral_map ((meas_expden κ).mul hf) meas_logabs]
  rfl

lemma exp_kappa_log_abs (κ x : ℝ) (hx : x ≠ 0) :
    Real.exp (κ * Real.log |x|) = |x| ^ κ := by
  rw [Real.rpow_def_of_pos (abs_pos.mpr hx), mul_comm]

lemma tiltOn_univ (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hs0 : s ⊆ {x | x ≠ 0}) :
    tiltOn κ μ s Set.univ = ∫⁻ x in s, ENNReal.ofReal (|x| ^ κ) ∂μ := by
  rw [← setLIntegral_one, setLIntegral_univ, lintegral_tiltOn κ μ s _ measurable_const]
  refine setLIntegral_congr_fun hs (fun x hx => ?_)
  rw [mul_one, exp_kappa_log_abs κ x (hs0 hx)]

lemma Ioi_ne : Set.Ioi (0:ℝ) ⊆ {x | x ≠ 0} := fun x hx => ne_of_gt hx
lemma Iio_ne : Set.Iio (0:ℝ) ⊆ {x | x ≠ 0} := fun x hx => ne_of_lt hx

lemma pPlus_eq (κ : ℝ) (μ : Measure ℝ) : pPlus κ μ = tiltOn κ μ (Set.Ioi 0) Set.univ := by
  rw [tiltOn_univ κ μ _ measurableSet_Ioi Ioi_ne]; rfl

lemma qMinus_eq (κ : ℝ) (μ : Measure ℝ) : qMinus κ μ = tiltOn κ μ (Set.Iio 0) Set.univ := by
  rw [tiltOn_univ κ μ _ measurableSet_Iio Iio_ne]; rfl

lemma pPlus_le (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) : pPlus κ μ ≤ 1 := by
  rw [← hC.moment_eq_one]; exact setLIntegral_le_lintegral _ _

lemma qMinus_le (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) : qMinus κ μ ≤ 1 := by
  rw [← hC.moment_eq_one]; exact setLIntegral_le_lintegral _ _

lemma smul_inv_smul_tilt (c : ℝ≥0∞) (ρ : Measure ℝ) (hc : c = ρ Set.univ) (htop : c ≠ ⊤) :
    c • (c⁻¹ • ρ) = ρ := by
  by_cases h0 : c = 0
  · have : ρ = 0 := Measure.measure_univ_eq_zero.mp (hc ▸ h0)
    simp [this]
  · rw [smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

lemma pPlus_smul (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) :
    pPlus κ μ • etaPlus κ μ = tiltOn κ μ (Set.Ioi 0) :=
  smul_inv_smul_tilt _ _ (pPlus_eq κ μ) (ne_top_of_le_ne_top ENNReal.one_ne_top (pPlus_le κ μ hC))

lemma qMinus_smul (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) :
    qMinus κ μ • etaMinus κ μ = tiltOn κ μ (Set.Iio 0) :=
  smul_inv_smul_tilt _ _ (qMinus_eq κ μ) (ne_top_of_le_ne_top ENNReal.one_ne_top (qMinus_le κ μ hC))

lemma convPow_sfinite (ρ : Measure ℝ) [SFinite ρ] : ∀ k, SFinite (convPow ρ k)
  | 0 => by simp only [convPow]; infer_instance
  | k + 1 => by
    have := convPow_sfinite ρ k
    simp only [convPow]; infer_instance

lemma convPow_smul (c : ℝ≥0∞) (ρ : Measure ℝ) [SFinite ρ] :
    ∀ k, convPow (c • ρ) k = c ^ k • convPow ρ k
  | 0 => by simp [convPow]
  | k + 1 => by
    have := convPow_sfinite ρ k
    simp only [convPow]
    rw [convPow_smul c ρ k, Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, pow_succ,
      mul_comm]

lemma etaCase2_eq (κ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (hC : CramerConditions κ μ) :
    etaCase2 κ μ = tiltOn κ μ (Set.Ioi 0) +
      Measure.sum (fun k : ℕ => (tiltOn κ μ (Set.Iio 0) ∗ tiltOn κ μ (Set.Iio 0)) ∗
        convPow (tiltOn κ μ (Set.Ioi 0)) k) := by
  unfold etaCase2
  rw [pPlus_smul κ μ hC]
  congr 2
  funext k
  have : SFinite (etaPlus κ μ) := by unfold etaPlus; infer_instance
  have : SFinite (etaMinus κ μ) := by unfold etaMinus; infer_instance
  have := convPow_sfinite (etaPlus κ μ) k
  have := convPow_sfinite (etaMinus κ μ) 2
  rw [← pPlus_smul κ μ hC, ← qMinus_smul κ μ hC, convPow_smul _ _ k]
  have h2' : convPow (etaMinus κ μ) 2 = etaMinus κ μ ∗ etaMinus κ μ := by
    simp only [convPow]; rw [Measure.conv_dirac_zero]
  rw [h2']
  simp only [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul]
  congr 1
  ring

lemma etaZero_eq (κ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (hC : CramerConditions κ μ) :
    etaZero κ μ = Measure.sum (fun k : ℕ => tiltOn κ μ (Set.Iio 0) ∗
        convPow (tiltOn κ μ (Set.Ioi 0)) k) := by
  unfold etaZero
  congr 1
  funext k
  have : SFinite (etaPlus κ μ) := by unfold etaPlus; infer_instance
  have : SFinite (etaMinus κ μ) := by unfold etaMinus; infer_instance
  have := convPow_sfinite (etaPlus κ μ) k
  rw [← pPlus_smul κ μ hC, ← qMinus_smul κ μ hC, convPow_smul _ _ k, Measure.conv_smul_left,
    Measure.conv_smul_right, smul_smul]

/-! ### Convolution of a nonnegative function with a measure -/

/-- `F ⊛ ρ (t) = ∫⁻ F(t - y) ρ(dy)` -/
noncomputable def cv (F : ℝ → ℝ≥0∞) (ρ : Measure ℝ) (t : ℝ) : ℝ≥0∞ := ∫⁻ y, F (t - y) ∂ρ

lemma cv_meas (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ : Measure ℝ) [SFinite ρ] :
    Measurable (cv F ρ) := by
  unfold cv
  exact (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'

lemma cv_conv (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    cv F (ρ ∗ σ) = cv (cv F σ) ρ := by
  funext t
  unfold cv
  rw [Measure.lintegral_conv (f := fun z => F (t - z))
    (hF.comp (measurable_const.sub measurable_id))]
  refine lintegral_congr (fun x => lintegral_congr (fun y => ?_))
  congr 1; ring

lemma cv_add_measure (F : ℝ → ℝ≥0∞) (ρ σ : Measure ℝ) : cv F (ρ + σ) = cv F ρ + cv F σ := by
  funext t; unfold cv; rw [lintegral_add_measure]; rfl

lemma cv_sum (F : ℝ → ℝ≥0∞) (ρs : ℕ → Measure ℝ) :
    cv F (Measure.sum ρs) = fun t => ∑' k, cv F (ρs k) t := by
  funext t; unfold cv; rw [lintegral_sum_measure]

lemma cv_add_fun (F G : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ : Measure ℝ) :
    cv (F + G) ρ = cv F ρ + cv G ρ := by
  funext t; unfold cv
  show ∫⁻ y, F (t - y) + G (t - y) ∂ρ = ∫⁻ y, F (t - y) ∂ρ + ∫⁻ y, G (t - y) ∂ρ
  exact lintegral_add_left (hF.comp (measurable_const.sub measurable_id) :
    Measurable fun z => F (t - z)) _

lemma cv_dirac (F : ℝ → ℝ≥0∞) : cv F (Measure.dirac 0) = F := by
  funext t; unfold cv; rw [lintegral_dirac]; simp

/-- **Algebraic identity behind (9.15)**: with `X = F⊛A + G⊛B`, `Y = G⊛A + F⊛B`,
`η = A + Σ_k (B∗B)∗A^k`, `η₀ = Σ_k B∗A^k`, one has `X + Y⊛η₀ = F⊛η + G⊛η₀`. -/
lemma key_algebra (F G : ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G)
    (A B : Measure ℝ) [SFinite A] [SFinite B] :
    (cv F A + cv G B) + cv (cv G A + cv F B) (Measure.sum (fun k : ℕ => B ∗ convPow A k)) =
      cv F (A + Measure.sum (fun k : ℕ => (B ∗ B) ∗ convPow A k)) +
        cv G (Measure.sum (fun k : ℕ => B ∗ convPow A k)) := by
  have := convPow_sfinite A
  have hGA : Measurable (cv G A) := cv_meas G hG A
  have hFB : Measurable (cv F B) := cv_meas F hF B
  -- expand `Y ⊛ (B ∗ A^k)`
  have hY : ∀ k, cv (cv G A + cv F B) (B ∗ convPow A k) =
      cv G (B ∗ convPow A (k + 1)) + cv F ((B ∗ B) ∗ convPow A k) := by
    intro k
    have := convPow_sfinite A k
    rw [cv_add_fun _ _ hGA, ← cv_conv G hG _ A, ← cv_conv F hF _ B]
    congr 2
    · simp only [convPow]
      rw [Measure.conv_assoc, Measure.conv_comm (convPow A k) A]
    · rw [Measure.conv_assoc, Measure.conv_comm (convPow A k) B, ← Measure.conv_assoc]
  funext t
  simp only [Pi.add_apply, cv_add_measure, cv_sum]
  simp only [hY, Pi.add_apply]
  rw [ENNReal.tsum_add]
  have hshift : ∑' k, cv G (B ∗ convPow A k) t =
      cv G B t + ∑' k, cv G (B ∗ convPow A (k + 1)) t := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [convPow]
    rw [Measure.conv_dirac_zero]
  rw [hshift]
  ring

/-! ### The tail functions in `[0, ∞]` -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `e^{κs} P(e^s < R)` in `[0,∞]` -/
noncomputable def Fp (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (κ * s)) * P {ω | Real.exp s < R ω}

lemma Fp_meas (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ) : Measurable (Fp P R κ) := by
  unfold Fp
  refine (meas_expden κ).mul ?_
  apply Antitone.measurable
  intro a b hab
  apply measure_mono
  intro ω hω
  exact lt_of_le_of_lt (Real.exp_le_exp.mpr hab) hω

lemma set_pos (t x : ℝ) (hx : 0 < x) (R : Ω → ℝ) :
    {ω | Real.exp t < x * R ω} = {ω | Real.exp (t - Real.log |x|) < R ω} := by
  rw [abs_of_pos hx, Real.exp_sub, Real.exp_log hx]
  ext ω
  change Real.exp t < x * R ω ↔ Real.exp t / x < R ω
  rw [div_lt_iff₀' hx]

lemma set_neg (t x : ℝ) (hx : x < 0) (R : Ω → ℝ) :
    {ω | Real.exp t < x * R ω} = {ω | Real.exp (t - Real.log |x|) < -R ω} := by
  rw [abs_of_neg hx, Real.exp_sub, Real.exp_log (neg_pos.mpr hx)]
  ext ω
  change Real.exp t < x * R ω ↔ Real.exp t / -x < -R ω
  rw [div_lt_iff₀ (neg_pos.mpr hx)]
  constructor <;> intro h <;> nlinarith

lemma ofReal_exp_split (κ t y : ℝ) :
    ENNReal.ofReal (Real.exp (κ * t)) =
      ENNReal.ofReal (Real.exp (κ * y)) * ENNReal.ofReal (Real.exp (κ * (t - y))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

/-- **(I1)**: `e^{κt} P(MR > e^t) = (r₊ ⊛ A)(t) + (r₋ ⊛ B)(t)` for `R` independent of `M`. -/
lemma tail_prod_eq (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hind : IndepFun R M P) (t : ℝ) :
    ENNReal.ofReal (Real.exp (κ * t)) * P {ω | Real.exp t < M ω * R ω} =
      cv (Fp P R κ) (tiltOn κ (P.map M) (Set.Ioi 0)) t +
        cv (Fp P (fun ω => -R ω) κ) (tiltOn κ (P.map M) (Set.Iio 0)) t := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hM.aemeasurable).mp hind
  set S : Set (ℝ × ℝ) := {p | Real.exp t < p.2 * p.1} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_snd.mul measurable_fst)
  have h1 : P {ω | Real.exp t < M ω * R ω} = ((P.map R).prod (P.map M)) S := by
    rw [← hmap, Measure.map_apply (hR.prodMk hM) hS]; rfl
  have hpre : ∀ x : ℝ, (P.map R) ((fun r => (r, x)) ⁻¹' S) = P {ω | Real.exp t < x * R ω} := by
    intro x
    rw [Measure.map_apply hR]
    · rfl
    · exact measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  rw [h1, Measure.prod_apply_symm hS]
  simp only [hpre]
  unfold cv
  rw [lintegral_tiltOn _ _ _ (fun y => Fp P R κ (t - y))
      ((Fp_meas P R κ).comp (measurable_const.sub measurable_id)),
    lintegral_tiltOn _ _ _ (fun y => Fp P (fun ω => -R ω) κ (t - y))
      ((Fp_meas P _ κ).comp (measurable_const.sub measurable_id)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_univ]
  have hu : (Set.univ : Set ℝ) = (Set.Ioi 0 ∪ Set.Iio 0) ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff,
      true_iff]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hd1 : Disjoint (Set.Ioi (0:ℝ) ∪ Set.Iio 0) {0} := by
    rw [Set.disjoint_singleton_right]
    simp
  have hd2 : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Set.mem_Ioi.mp h1) (Set.mem_Iio.mp h2)
  rw [hu, lintegral_union (measurableSet_singleton 0) hd1,
    lintegral_union measurableSet_Iio hd2, lintegral_singleton]
  have h0 : {ω | Real.exp t < (0:ℝ) * R ω} = ∅ := by
    ext ω
    simp only [zero_mul, Set.mem_empty_iff_false, iff_false]
    exact fun h => absurd h (not_lt.mpr (Real.exp_pos t).le)
  rw [h0, measure_empty, mul_zero, zero_mul, add_zero]
  congr 1
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Function.comp, Fp]
    rw [set_pos t x hx R, ← mul_assoc, ← ofReal_exp_split]
  · refine setLIntegral_congr_fun measurableSet_Iio (fun x hx => ?_)
    simp only [Function.comp, Fp]
    rw [set_neg t x hx R, ← mul_assoc, ← ofReal_exp_split]

/-! ### exponential moments `Lc c ρ = ∫⁻ e^{c y} ρ(dy)` -/

noncomputable def Lc (c : ℝ) (ρ : Measure ℝ) : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (Real.exp (c * y)) ∂ρ

lemma Lc_tilt (κ c : ℝ) (μ : Measure ℝ) (s : Set ℝ) :
    Lc c (tiltOn κ μ s) = ∫⁻ x in s, ENNReal.ofReal (Real.exp ((κ + c) * Real.log |x|)) ∂μ := by
  unfold Lc
  rw [lintegral_tiltOn _ _ _ _ (meas_expden c)]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_mul]

lemma Lc_conv (c : ℝ) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    Lc c (ρ ∗ σ) = Lc c ρ * Lc c σ := by
  unfold Lc
  rw [Measure.lintegral_conv (meas_expden c)]
  have : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (c * (x + y))) =
      ENNReal.ofReal (Real.exp (c * x)) * ENNReal.ofReal (Real.exp (c * y)) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
  simp only [this]
  simp only [lintegral_const_mul _ (meas_expden c)]
  rw [lintegral_mul_const _ (meas_expden c)]

lemma Lc_dirac (c : ℝ) : Lc c (Measure.dirac 0) = 1 := by
  unfold Lc; rw [lintegral_dirac]; simp

lemma Lc_convPow (c : ℝ) (ρ : Measure ℝ) [SFinite ρ] : ∀ k, Lc c (convPow ρ k) = Lc c ρ ^ k
  | 0 => by simp only [convPow, pow_zero]; exact Lc_dirac c
  | k + 1 => by
    have := convPow_sfinite ρ k
    simp only [convPow]
    rw [Lc_conv, Lc_convPow c ρ k, pow_succ, mul_comm]

lemma Lc_add (c : ℝ) (ρ σ : Measure ℝ) : Lc c (ρ + σ) = Lc c ρ + Lc c σ := by
  unfold Lc; rw [lintegral_add_measure]

lemma Lc_sum (c : ℝ) (ρs : ℕ → Measure ℝ) : Lc c (Measure.sum ρs) = ∑' k, Lc c (ρs k) := by
  unfold Lc; rw [lintegral_sum_measure]

lemma Lc_zero_eq_univ (ρ : Measure ℝ) : Lc 0 ρ = ρ Set.univ := by
  unfold Lc; simp

/-- The mass computation for the law `η = A + Σ_k (B∗B)∗A^k`. -/
lemma Lc_eta (c : ℝ) (A B : Measure ℝ) [SFinite A] [SFinite B] :
    Lc c (A + Measure.sum (fun k : ℕ => (B ∗ B) ∗ convPow A k)) =
      Lc c A + Lc c B ^ 2 * (1 - Lc c A)⁻¹ := by
  have := convPow_sfinite A
  rw [Lc_add, Lc_sum]
  congr 1
  have : ∀ k, Lc c ((B ∗ B) ∗ convPow A k) = Lc c B ^ 2 * Lc c A ^ k := by
    intro k
    have := convPow_sfinite A k
    rw [Lc_conv, Lc_conv, Lc_convPow, sq]
  simp only [this]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma Lc_etaZero (c : ℝ) (A B : Measure ℝ) [SFinite A] [SFinite B] :
    Lc c (Measure.sum (fun k : ℕ => B ∗ convPow A k)) = Lc c B * (1 - Lc c A)⁻¹ := by
  have := convPow_sfinite A
  rw [Lc_sum]
  have : ∀ k, Lc c (B ∗ convPow A k) = Lc c B * Lc c A ^ k := by
    intro k
    have := convPow_sfinite A k
    rw [Lc_conv, Lc_convPow]
  simp only [this]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- `a + b²(1-a)⁻¹ ≤ 1` and `b (1-a)⁻¹ ≤ 1` whenever `a + b ≤ 1`. -/
lemma mass_le_one (a b : ℝ≥0∞) (hab : a + b ≤ 1) : a + b ^ 2 * (1 - a)⁻¹ ≤ 1 ∧ b * (1 - a)⁻¹ ≤ 1 := by
  have ha : a ≤ 1 := le_trans le_self_add hab
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hb : b ≤ 1 - a := ENNReal.le_sub_of_add_le_left hat hab
  by_cases hb0 : b = 0
  · subst hb0; simp [ha]
  have h1a : (1 - a) ≠ 0 := by
    intro h; rw [h] at hb; exact hb0 (le_antisymm hb zero_le)
  have h1at : (1 - a) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hbb : b * (1 - a)⁻¹ ≤ 1 := by
    calc b * (1 - a)⁻¹ ≤ (1 - a) * (1 - a)⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel h1a h1at
  refine ⟨?_, hbb⟩
  calc a + b ^ 2 * (1 - a)⁻¹ = a + b * (b * (1 - a)⁻¹) := by rw [sq, mul_assoc]
    _ ≤ a + b * 1 := by gcongr
    _ = a + b := by rw [mul_one]
    _ ≤ 1 := hab

/-! ### The auxiliary law `μ̃` with tilted law `η` -/

/-- `ν₁ = exp_* (e^{-κy} η(dy))` -/
noncomputable def nuOne (κ : ℝ) (η : Measure ℝ) : Measure ℝ :=
  (η.withDensity (fun y => ENNReal.ofReal (Real.exp (-κ * y)))).map Real.exp

/-- `μ̃ = ν₁ + (1 - ν₁(ℝ)) δ₀` -/
noncomputable def muT (κ : ℝ) (η : Measure ℝ) : Measure ℝ :=
  nuOne κ η + (1 - nuOne κ η Set.univ) • Measure.dirac 0

lemma nuOne_univ (κ : ℝ) (η : Measure ℝ) : nuOne κ η Set.univ = Lc (-κ) η := by
  unfold nuOne Lc
  rw [Measure.map_apply Real.measurable_exp MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma muT_prob (κ : ℝ) (η : Measure ℝ) (hL : Lc (-κ) η ≤ 1) : IsProbabilityMeasure (muT κ η) := by
  constructor
  unfold muT
  rw [Measure.add_apply, Measure.smul_apply, nuOne_univ, measure_univ, smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le hL

lemma nuOne_compl (κ : ℝ) (η : Measure ℝ) : nuOne κ η (Set.Ioi 0)ᶜ = 0 := by
  unfold nuOne
  rw [Measure.map_apply Real.measurable_exp measurableSet_Ioi.compl]
  have : Real.exp ⁻¹' (Set.Ioi 0)ᶜ = ∅ := by
    ext y; simp [Real.exp_pos]
  rw [this, measure_empty]

lemma muT_restrict_Ioi (κ : ℝ) (η : Measure ℝ) : (muT κ η).restrict (Set.Ioi 0) = nuOne κ η := by
  unfold muT
  rw [Measure.restrict_add, Measure.restrict_smul, restrict_dirac' measurableSet_Ioi]
  simp only [Set.mem_Ioi, lt_irrefl, if_false, smul_zero, add_zero]
  exact Measure.restrict_eq_self_of_ae_mem ((ae_iff).mpr (nuOne_compl κ η))

lemma muT_restrict_Iio (κ : ℝ) (η : Measure ℝ) : (muT κ η).restrict (Set.Iio 0) = 0 := by
  unfold muT
  rw [Measure.restrict_add, Measure.restrict_smul, restrict_dirac' measurableSet_Iio]
  simp only [Set.mem_Iio, lt_irrefl, if_false, smul_zero, add_zero]
  apply Measure.restrict_eq_zero.mpr
  refine measure_mono_null (fun x hx => ?_) (nuOne_compl κ η)
  simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
  exact (Set.mem_Iio.mp hx).le

lemma muT_restrict_ne (κ : ℝ) (η : Measure ℝ) :
    (muT κ η).restrict {x | x ≠ 0} = nuOne κ η := by
  have hm : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
  unfold muT
  rw [Measure.restrict_add, Measure.restrict_smul, restrict_dirac' hm]
  simp only [Set.mem_ofPred_eq, ne_eq, not_true_eq_false, if_false, smul_zero, add_zero]
  apply Measure.restrict_eq_self_of_ae_mem
  refine (ae_iff).mpr (measure_mono_null (fun x hx => ?_) (nuOne_compl κ η))
  simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hx
  simp [hx]

lemma logabs_exp : (fun x : ℝ => Real.log |x|) ∘ Real.exp = id := by
  funext y
  simp [abs_of_pos (Real.exp_pos y), Real.log_exp]

lemma map_logabs_nuOne (κ : ℝ) (η : Measure ℝ) :
    (nuOne κ η).map (fun x => Real.log |x|) =
      η.withDensity (fun y => ENNReal.ofReal (Real.exp (-κ * y))) := by
  unfold nuOne
  rw [Measure.map_map meas_logabs Real.measurable_exp, logabs_exp, Measure.map_id]

lemma tiltOn_muT_Ioi (κ : ℝ) (η : Measure ℝ) : tiltOn κ (muT κ η) (Set.Ioi 0) = η := by
  unfold tiltOn
  rw [muT_restrict_Ioi, map_logabs_nuOne, ← withDensity_mul _ (meas_expden (-κ)) (meas_expden κ)]
  have : (fun y : ℝ => ENNReal.ofReal (Real.exp (-κ * y))) *
      (fun u : ℝ => ENNReal.ofReal (Real.exp (κ * u))) = 1 := by
    funext y
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [this, withDensity_one]

lemma tiltOn_muT_Iio (κ : ℝ) (η : Measure ℝ) : tiltOn κ (muT κ η) (Set.Iio 0) = 0 := by
  unfold tiltOn
  rw [muT_restrict_Iio]
  simp

/-- `∫⁻ f dμ̃ = ∫⁻ e^{-κy} f(e^y) η(dy) + (1 - ν₁(ℝ)) f(0)` -/
lemma lintegral_muT (κ : ℝ) (η : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(muT κ η) =
      ∫⁻ y, ENNReal.ofReal (Real.exp (-κ * y)) * f (Real.exp y) ∂η +
        (1 - nuOne κ η Set.univ) * f 0 := by
  unfold muT
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  congr 1
  unfold nuOne
  rw [lintegral_map hf Real.measurable_exp]
  exact lintegral_withDensity_eq_lintegral_mul η (meas_expden (-κ)) (hf.comp Real.measurable_exp)

lemma muT_cramer (κ : ℝ) (hκ : 0 < κ) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hint : Integrable (fun y : ℝ => y) η) (hna : ¬ IsArithmetic η) (hL : Lc (-κ) η ≤ 1) :
    CramerConditions κ (muT κ η) := by
  have hprob := muT_prob κ η hL
  have hexp : ∀ y : ℝ, |Real.exp y| ^ κ = Real.exp (κ * y) := by
    intro y
    rw [abs_of_pos (Real.exp_pos y), ← Real.exp_mul, mul_comm]
  have hcancel : ∀ y : ℝ, ENNReal.ofReal (Real.exp (-κ * y)) * ENNReal.ofReal (Real.exp (κ * y)) = 1 := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have h0 : (0:ℝ) ^ κ = 0 := Real.zero_rpow hκ.ne'
  refine ⟨measure_univ, hκ, ?_, ?_, ?_⟩
  · rw [lintegral_muT κ η (fun x => ENNReal.ofReal (|x| ^ κ))
      (continuous_abs.measurable.pow_const κ).ennreal_ofReal]
    simp only [hexp, hcancel, abs_zero, h0, ENNReal.ofReal_zero, mul_zero, add_zero]
    simp
  · rw [lintegral_muT κ η (fun x => ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0))
      ((continuous_abs.measurable.pow_const κ).mul
      ((meas_logabs).max measurable_const)).ennreal_ofReal]
    simp only [abs_zero, h0, zero_mul, ENNReal.ofReal_zero, mul_zero, add_zero]
    have : ∀ y : ℝ, ENNReal.ofReal (Real.exp (-κ * y)) *
        ENNReal.ofReal (|Real.exp y| ^ κ * max (Real.log |Real.exp y|) 0) =
          ENNReal.ofReal (max y 0) := by
      intro y
      rw [hexp, abs_of_pos (Real.exp_pos y), Real.log_exp,
        ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, hcancel, one_mul]
    simp only [this]
    refine lt_of_le_of_lt (lintegral_mono (fun y => ?_)) hint.hasFiniteIntegral
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (max_le (le_abs_self y) (abs_nonneg y))
  · intro harith
    apply hna
    obtain ⟨l, hl, hL0⟩ := harith
    refine ⟨l, hl, ?_⟩
    have hLm : MeasurableSet (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ :=
      (Set.countable_range _).measurableSet.compl
    have hne : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
    unfold ProbabilityTheory.cond at hL0
    rw [muT_restrict_ne, Measure.map_smul, map_logabs_nuOne, Measure.smul_apply, smul_eq_mul,
      mul_eq_zero] at hL0
    rcases hL0 with h | h
    · exfalso
      rw [ENNReal.inv_eq_zero] at h
      exact measure_ne_top _ _ h
    · rw [withDensity_apply_eq_zero' (meas_expden (-κ)).aemeasurable] at h
      have hall : {x : ℝ | ENNReal.ofReal (Real.exp (-κ * x)) ≠ 0} = Set.univ := by
        ext x; simp [Real.exp_pos]
      rwa [hall, Set.univ_inter] at h

lemma cramerMean_muT (κ : ℝ) (hκ : 0 < κ) (η : Measure ℝ) (hint : Integrable (fun y : ℝ => y) η) :
    cramerMean κ (muT κ η) = ∫ y, y ∂η := by
  have hexp : ∀ y : ℝ, |Real.exp y| ^ κ = Real.exp (κ * y) := by
    intro y
    rw [abs_of_pos (Real.exp_pos y), ← Real.exp_mul, mul_comm]
  have h0 : (0:ℝ) ^ κ = 0 := Real.zero_rpow hκ.ne'
  set f : ℝ → ℝ := fun x => |x| ^ κ * Real.log |x| with hfdef
  have hfm : Measurable f := (continuous_abs.measurable.pow_const κ).mul meas_logabs
  have hlt : ∀ᵐ y ∂η, ENNReal.ofReal (Real.exp (-κ * y)) < ∞ :=
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  have hcomp : ∀ y : ℝ, (ENNReal.ofReal (Real.exp (-κ * y))).toReal • f (Real.exp y) = y := by
    intro y
    show (ENNReal.ofReal (Real.exp (-κ * y))).toReal * (|Real.exp y| ^ κ * Real.log |Real.exp y|) = y
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hexp, abs_of_pos (Real.exp_pos y), Real.log_exp,
      ← mul_assoc, ← Real.exp_add]
    simp
  have hint1 : Integrable f (nuOne κ η) := by
    unfold nuOne
    rw [integrable_map_measure hfm.aestronglyMeasurable Real.measurable_exp.aemeasurable,
      integrable_withDensity_iff_integrable_smul' (meas_expden (-κ)) hlt]
    simpa only [Function.comp, hcomp] using hint
  have hint2 : Integrable f ((1 - nuOne κ η Set.univ) • Measure.dirac (0:ℝ)) := by
    refine Integrable.smul_measure ?_ (ENNReal.sub_ne_top ENNReal.one_ne_top)
    exact integrable_dirac enorm_lt_top
  unfold cramerMean muT
  rw [integral_add_measure hint1 hint2, integral_smul_measure, integral_dirac]
  simp only [hfdef, abs_zero, h0, zero_mul, smul_zero, add_zero]
  unfold nuOne
  rw [integral_map Real.measurable_exp.aemeasurable hfm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (meas_expden (-κ)) hlt]
  exact integral_congr_ae (Filter.Eventually.of_forall hcomp)


/-! ### Case 2: the tail identity on the product space -/

lemma Fp_toReal (P : Measure Ω) (X : Ω → ℝ) (κ t : ℝ) :
    (Fp P X κ t).toReal = Real.exp (κ * t) * P.real {ω | Real.exp t < X ω} := by
  unfold Fp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

lemma gOne_eq_Fp (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    gOne P M R κ = fun t => (Fp P R κ t).toReal - (Fp P (fun ω => M ω * R ω) κ t).toReal := by
  funext t
  rw [Fp_toReal, Fp_toReal]
  unfold gOne
  ring

lemma gNegOne_eq (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    gNegOne P M R κ = gOne P M (fun ω => -R ω) κ := by
  funext t
  unfold gOne gNegOne
  have h1 : {ω | Real.exp t < -R ω} = {ω | R ω < -Real.exp t} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have h2 : {ω | Real.exp t < M ω * -R ω} = {ω | M ω * R ω < -Real.exp t} := by
    ext ω; simp only [Set.mem_ofPred_eq, mul_neg]; constructor <;> intro h <;> linarith
  rw [h1, h2]

lemma tailCond_iff (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    TailCondPlus P M R κ ↔ Integrable (gOne P M R κ) := by
  unfold TailCondPlus
  rw [integrableOn_Ioi_iff_exp]
  simp only [exp_mul_tailDiffPlus]

lemma gOne_meas (P : Measure Ω) [IsFiniteMeasure P] (M R : Ω → ℝ) (κ : ℝ) :
    Measurable (gOne P M R κ) := by
  rw [gOne_eq_Fp]
  exact ((Fp_meas P R κ).ennreal_toReal).sub ((Fp_meas P _ κ).ennreal_toReal)

lemma Fp_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (κ s : ℝ) :
    Fp P X κ s ≤ ENNReal.ofReal (Real.exp (κ * s)) := by
  unfold Fp
  exact mul_le_of_le_one_right zero_le prob_le_one

lemma cv_le_exp (F : ℝ → ℝ≥0∞) (κ : ℝ) (hF : ∀ s, F s ≤ ENNReal.ofReal (Real.exp (κ * s)))
    (ρ : Measure ℝ) (t : ℝ) :
    cv F ρ t ≤ ENNReal.ofReal (Real.exp (κ * t)) * Lc (-κ) ρ := by
  unfold cv Lc
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun y => le_trans (hF _) (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

lemma cv_zero_measure (F : ℝ → ℝ≥0∞) : cv F 0 = 0 := by
  funext t; unfold cv; simp

lemma conv_fin_integrable (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    Integrable (fun t => ∫ y, g (t - y) ∂ρ) ∧
      ∫ t, (∫ y, g (t - y) ∂ρ) = ρ.real Set.univ * ∫ t, g t := by
  have hF : Integrable (fun p : ℝ × ℝ => g (p.1 - p.2)) (volume.prod ρ) := by
    rw [integrable_prod_iff' (f := fun p : ℝ × ℝ => g (p.1 - p.2))
      (hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun y => hg.comp_sub_right y), ?_⟩
    have : ∀ y : ℝ, ∫ x, ‖g (x - y)‖ = ∫ x, ‖g x‖ :=
      fun y => integral_sub_right_eq_self (fun x => ‖g x‖) y
    simp only [this]
    exact integrable_const _
  refine ⟨hF.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun t y => g (t - y)) hF]
  have : ∀ y : ℝ, ∫ x, g (x - y) = ∫ x, g x := fun y => integral_sub_right_eq_self g y
  simp only [this, integral_const, smul_eq_mul]

lemma prod_fst_real (P : Measure Ω) (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Set Ω)
    (hS : MeasurableSet S) : (P.prod ν).real {p | p.1 ∈ S} = P.real S := by
  have h := Measure.map_fst_prod (μ := P) (ν := ν)
  rw [measure_univ, one_smul] at h
  unfold Measure.real
  show ((P.prod ν) (Prod.fst ⁻¹' S)).toReal = (P S).toReal
  rw [← Measure.map_apply measurable_fst hS, h]

lemma prod_fst_meas (P : Measure Ω) (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Set Ω)
    (hS : MeasurableSet S) : (P.prod ν) {p | p.1 ∈ S} = P S := by
  have h := Measure.map_fst_prod (μ := P) (ν := ν)
  rw [measure_univ, one_smul] at h
  show (P.prod ν) (Prod.fst ⁻¹' S) = P S
  rw [← Measure.map_apply measurable_fst hS, h]

lemma Fp_prod (P : Measure Ω) (ν : Measure ℝ) [IsProbabilityMeasure ν] (R : Ω → ℝ) (hR : Measurable R)
    (κ : ℝ) : Fp (P.prod ν) (fun p => R p.1) κ = Fp P R κ := by
  funext s
  unfold Fp
  rw [← prod_fst_meas P ν {ω | Real.exp s < R ω} (measurableSet_lt measurable_const hR)]
  rfl

lemma Lc_tilt_neg (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    Lc (-κ) (tiltOn κ μ s) = μ s := by
  rw [Lc_tilt]
  simp only [add_neg_cancel, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
  rw [setLIntegral_const, one_mul]

lemma pq_sum (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) :
    pPlus κ μ + qMinus κ μ = 1 := by
  rw [← hC.moment_eq_one, ← setLIntegral_univ]
  have hu : (Set.univ : Set ℝ) = (Set.Ioi 0 ∪ Set.Iio 0) ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff,
      true_iff]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hd1 : Disjoint (Set.Ioi (0:ℝ) ∪ Set.Iio 0) {0} := by
    rw [Set.disjoint_singleton_right]; simp
  have hd2 : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Set.mem_Ioi.mp h1) (Set.mem_Iio.mp h2)
  rw [hu, lintegral_union (measurableSet_singleton 0) hd1,
    lintegral_union measurableSet_Iio hd2, lintegral_singleton]
  simp [Real.zero_rpow hC.pos.ne', pPlus, qMinus]

lemma qMinus_ne_zero (κ : ℝ) (μ : Measure ℝ) (hC : CramerConditions κ μ) (hneg : 0 < μ (Set.Iio 0)) :
    qMinus κ μ ≠ 0 := by
  intro h
  unfold qMinus at h
  rw [lintegral_eq_zero_iff ((continuous_abs.measurable.pow_const κ).ennreal_ofReal)] at h
  have h2 : (μ.restrict (Set.Iio 0)) {x | ENNReal.ofReal (|x| ^ κ) ≠ 0} = 0 := by
    have := h
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  rw [Measure.restrict_apply' measurableSet_Iio] at h2
  have h3 : {x : ℝ | ENNReal.ofReal (|x| ^ κ) ≠ 0} ∩ Set.Iio 0 = Set.Iio 0 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, and_iff_right_iff_imp]
    intro hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (abs_pos.mpr hx.ne) κ
  rw [h3] at h2
  exact (ne_of_gt hneg) h2


lemma mass_Ioi_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ] : μ (Set.Ioi 0) + μ (Set.Iio 0) ≤ 1 := by
  have hd : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Set.mem_Ioi.mp h1) (Set.mem_Iio.mp h2)
  rw [← measure_union hd measurableSet_Iio]
  exact prob_le_one

lemma eta_mass (κ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hC : CramerConditions κ μ) :
    Lc (-κ) (etaCase2 κ μ) ≤ 1 ∧ Lc (-κ) (etaZero κ μ) ≤ 1 := by
  rw [etaCase2_eq κ μ hC, etaZero_eq κ μ hC, Lc_eta, Lc_etaZero,
    Lc_tilt_neg _ _ _ measurableSet_Ioi, Lc_tilt_neg _ _ _ measurableSet_Iio]
  exact mass_le_one _ _ (mass_Ioi_Iio μ)

lemma etaZero_univ (κ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hC : CramerConditions κ μ)
    (hneg : 0 < μ (Set.Iio 0)) : etaZero κ μ Set.univ = 1 := by
  rw [← Lc_zero_eq_univ, etaZero_eq κ μ hC, Lc_etaZero, Lc_zero_eq_univ, Lc_zero_eq_univ,
    ← pPlus_eq, ← qMinus_eq]
  have hpq := pq_sum κ μ hC
  have hq := qMinus_ne_zero κ μ hC hneg
  have hpt : pPlus κ μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (pPlus_le κ μ hC)
  have hqt : qMinus κ μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (qMinus_le κ μ hC)
  have : 1 - pPlus κ μ = qMinus κ μ := by rw [← hpq]; exact ENNReal.add_sub_cancel_left hpt
  rw [this, ENNReal.mul_inv_cancel hq hqt]

lemma real_abs_split (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X) (t : ℝ)
    (ht : 0 < t) :
    P.real {ω | t < |X ω|} = P.real {ω | t < X ω} + P.real {ω | X ω < -t} := by
  have h : {ω | t < |X ω|} = {ω | t < X ω} ∪ {ω | X ω < -t} := by
    ext ω
    simp only [Set.mem_union, Set.mem_ofPred_eq, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  have hd : Disjoint {ω | t < X ω} {ω | X ω < -t} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  rw [h, measureReal_union hd (measurableSet_lt hX measurable_const)]

lemma tailDiffAbs_eq (P : Measure Ω) [IsFiniteMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ t : ℝ) (ht : 0 < t) :
    tailDiffAbs P M R κ t = tailDiffPlus P M R κ t + tailDiffMinus P M R κ t := by
  unfold tailDiffAbs tailDiffPlus tailDiffMinus
  rw [real_abs_split P R hR t ht, real_abs_split P (fun ω => M ω * R ω) (hM.mul hR) t ht]
  ring

theorem case2_tail (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hneg : 0 < P {ω | M ω < 0}) (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    TailCondPlus (P.prod (muT κ (etaCase2 κ (P.map M)))) Prod.snd (fun p => R p.1) κ ∧
      ∫ t in Set.Ioi 0,
          tailDiffPlus (P.prod (muT κ (etaCase2 κ (P.map M)))) Prod.snd (fun p => R p.1) κ t =
        ∫ t in Set.Ioi 0, tailDiffAbs P M R κ t := by
  set μ := P.map M with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hM.aemeasurable
  have hnegμ : 0 < μ (Set.Iio 0) := by
    rw [hμ, Measure.map_apply hM measurableSet_Iio]; exact hneg
  obtain ⟨hLη, hLη₀⟩ := eta_mass κ μ hC
  set η := etaCase2 κ μ with hηdef
  set η₀ := etaZero κ μ with hη₀def
  have : IsProbabilityMeasure (muT κ η) := muT_prob κ η hLη
  have : IsFiniteMeasure η₀ := ⟨by rw [hη₀def, etaZero_univ κ μ hC hnegμ]; exact ENNReal.one_lt_top⟩
  set A := tiltOn κ μ (Set.Ioi 0) with hA
  set B := tiltOn κ μ (Set.Iio 0) with hB
  have hX : Fp P (fun ω => M ω * R ω) κ = cv (Fp P R κ) A + cv (Fp P (fun ω => -R ω) κ) B :=
    funext (fun t => tail_prod_eq P M R hM hR κ hind t)
  have hindn : IndepFun (fun ω => -R ω) M P := hind.comp measurable_neg measurable_id
  have hY : Fp P (fun ω => M ω * -R ω) κ = cv (Fp P (fun ω => -R ω) κ) A + cv (Fp P R κ) B := by
    funext t
    have := tail_prod_eq P M (fun ω => -R ω) hM hR.neg κ hindn t
    simp only [neg_neg] at this
    exact this
  have hkey := key_algebra (Fp P R κ) (Fp P (fun ω => -R ω) κ) (Fp_meas _ _ _) (Fp_meas _ _ _) A B
  rw [← hX, ← hY, ← etaCase2_eq κ μ hC, ← etaZero_eq κ μ hC] at hkey
  set P' := P.prod (muT κ η) with hP'
  have hind' : IndepFun (fun p : Ω × ℝ => R p.1) Prod.snd P' := indepFun_prod hR measurable_id
  have hmap' : P'.map Prod.snd = muT κ η := by rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hZ : Fp P' (fun p => p.2 * R p.1) κ = cv (Fp P R κ) η := by
    funext t
    have := tail_prod_eq P' Prod.snd (fun p => R p.1) measurable_snd (hR.comp measurable_fst) κ
      hind' t
    rw [hmap', tiltOn_muT_Ioi, tiltOn_muT_Iio, cv_zero_measure, Fp_prod P _ R hR] at this
    simp only [Pi.zero_apply, add_zero] at this
    exact this
  have hfin : ∀ (F : ℝ → ℝ≥0∞), (∀ s, F s ≤ ENNReal.ofReal (Real.exp (κ * s))) →
      ∀ ρ : Measure ℝ, Lc (-κ) ρ ≤ 1 → ∀ t, cv F ρ t ≠ ⊤ := by
    intro F hF ρ hρ t
    refine ne_top_of_le_ne_top ?_ (cv_le_exp F κ hF ρ t)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hρ)
  have hgNeg_int : Integrable (gNegOne P M R κ) := by
    rw [gNegOne_eq, ← tailCond_iff]; unfold TailCondPlus; rw [tailDiffPlus_neg]; exact h29
  have hgNeg_meas : Measurable (gNegOne P M R κ) := by rw [gNegOne_eq]; exact gOne_meas _ _ _ _
  have hconv := conv_fin_integrable (gNegOne P M R κ) hgNeg_meas hgNeg_int η₀
  have hcvint : ∀ (X : Ω → ℝ) (t : ℝ),
      ∫ y, (Fp P X κ (t - y)).toReal ∂η₀ = (cv (Fp P X κ) η₀ t).toReal := by
    intro X t
    unfold cv
    exact integral_toReal ((Fp_meas P X κ).comp (measurable_const.sub measurable_id)).aemeasurable
      (Filter.Eventually.of_forall (fun y => lt_of_le_of_lt (Fp_le P X κ _) ENNReal.ofReal_lt_top))
  have hcvI : ∀ (X : Ω → ℝ) (t : ℝ), Integrable (fun y => (Fp P X κ (t - y)).toReal) η₀ := by
    intro X t
    exact integrable_toReal_of_lintegral_ne_top
      ((Fp_meas P X κ).comp (measurable_const.sub measurable_id)).aemeasurable
      (hfin _ (Fp_le P X κ) η₀ hLη₀ t)
  have hident : gOne P' Prod.snd (fun p => R p.1) κ =
      fun t => gOne P M R κ t + ∫ y, gNegOne P M R κ (t - y) ∂η₀ := by
    funext t
    have hn : ∫ y, gNegOne P M R κ (t - y) ∂η₀ =
        (cv (Fp P (fun ω => -R ω) κ) η₀ t).toReal -
          (cv (Fp P (fun ω => M ω * -R ω) κ) η₀ t).toReal := by
      rw [gNegOne_eq, gOne_eq_Fp]
      rw [integral_sub (hcvI _ t) (hcvI _ t), hcvint, hcvint]
    rw [hn, gOne_eq_Fp, gOne_eq_Fp]
    simp only
    rw [Fp_prod P _ R hR, hZ]
    have ht := congrFun hkey t
    simp only [Pi.add_apply] at ht
    have hXt : Fp P (fun ω => M ω * R ω) κ t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Fp_le P _ κ t)
    have hYt := hfin _ (Fp_le P (fun ω => M ω * -R ω) κ) η₀ hLη₀ t
    have hRt := hfin _ (Fp_le P R κ) η hLη t
    have hNt := hfin _ (Fp_le P (fun ω => -R ω) κ) η₀ hLη₀ t
    have ht' := congrArg ENNReal.toReal ht
    rw [ENNReal.toReal_add hXt hYt, ENNReal.toReal_add hRt hNt] at ht'
    linarith
  refine ⟨?_, ?_⟩
  · rw [tailCond_iff, hident]
    exact ((tailCond_iff P M R κ).mp h28).add hconv.1
  · rw [← integral_gOne, hident, integral_add ((tailCond_iff P M R κ).mp h28) hconv.1, hconv.2]
    have h1 : η₀.real Set.univ = 1 := by
      rw [measureReal_def, hη₀def, etaZero_univ κ μ hC hnegμ, ENNReal.toReal_one]
    rw [h1, one_mul, integral_gOne, gNegOne_eq, integral_gOne, tailDiffPlus_neg,
      ← integral_add h28 h29]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact (tailDiffAbs_eq P M R hM hR κ t ht).symm


/-- the four properties of `η` (9.11)–(9.13) used in Case 2 -/
def EtaFacts (κ : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure (etaCase2 κ μ) ∧ Integrable (fun y : ℝ => y) (etaCase2 κ μ) ∧
    ∫ y, y ∂(etaCase2 κ μ) = 2 * cramerMean κ μ ∧ ¬ IsArithmetic (etaCase2 κ μ)

/-- **Case 2, right tail**: Case 1 applied on `P ⊗ μ̃` with `M̃ = x`, `R̃ = R`. -/
theorem case2_plus (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hneg : 0 < P {ω | M ω < 0}) (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ)
    (hF : EtaFacts κ (P.map M)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Ctwo P M R κ)) := by
  obtain ⟨hηp, hint, hmean, hna⟩ := hF
  have : IsProbabilityMeasure (P.map M) := Measure.isProbabilityMeasure_map hM.aemeasurable
  obtain ⟨hLη, -⟩ := eta_mass κ (P.map M) hC
  set η := etaCase2 κ (P.map M) with hηdef
  have : IsProbabilityMeasure (muT κ η) := muT_prob κ η hLη
  obtain ⟨h28', hint'⟩ := case2_tail P M R hM hR κ hC hind hneg h28 h29
  set P' := P.prod (muT κ η) with hP'
  have hmap' : P'.map Prod.snd = muT κ η := by rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hC' : CramerConditions κ (P'.map Prod.snd) := by
    rw [hmap']; exact muT_cramer κ hC.pos η hint hna hLη
  have hind' : IndepFun (fun p : Ω × ℝ => R p.1) Prod.snd P' := indepFun_prod hR measurable_id
  have hnn : ∀ᵐ p ∂P', 0 ≤ p.2 := by
    rw [ae_iff]
    have h1 : (muT κ η) (Set.Iio 0) = 0 := by
      have := congrArg (fun m : Measure ℝ => m Set.univ) (muT_restrict_Iio κ η)
      simpa using this
    have h2 : {p : Ω × ℝ | ¬ 0 ≤ p.2} = Prod.snd ⁻¹' (Set.Iio 0) := by
      ext p; simp
    rw [h2, ← Measure.map_apply measurable_snd measurableSet_Iio, hmap', h1]
  have key := case1_plus P' Prod.snd (fun p => R p.1) measurable_snd (hR.comp measurable_fst) κ
    hC' hind' hnn h28'
  have hCeq : Cplus P' Prod.snd (fun p => R p.1) κ = Ctwo P M R κ := by
    unfold Cplus Ctwo
    rw [hmap', cramerMean_muT κ hC.pos η hint, hmean, hint']
  rw [hCeq] at key
  refine key.congr (fun t => ?_)
  congr 1
  exact prod_fst_real P (muT κ η) {ω | t < R ω} (measurableSet_lt measurable_const hR)

lemma tailDiffAbs_neg (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) :
    tailDiffAbs P M (fun ω => -R ω) κ = tailDiffAbs P M R κ := by
  funext t
  unfold tailDiffAbs
  simp only [abs_neg, mul_neg]

/-- **Case 2, left tail**: Case 2 right tail for `-R`. -/
theorem case2_minus (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hneg : 0 < P {ω | M ω < 0}) (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ)
    (hF : EtaFacts κ (P.map M)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Ctwo P M R κ)) := by
  have hind' : IndepFun (fun ω => -R ω) M P := hind.comp measurable_neg measurable_id
  have h28' : TailCondPlus P M (fun ω => -R ω) κ := by
    unfold TailCondPlus; rw [tailDiffPlus_neg]; exact h29
  have h29' : TailCondMinus P M (fun ω => -R ω) κ := by
    unfold TailCondMinus
    have : tailDiffMinus P M (fun ω => -R ω) κ = tailDiffPlus P M R κ := by
      have h := tailDiffPlus_neg P M (fun ω => -R ω) κ
      simp only [neg_neg] at h
      exact h.symm
    rw [this]; exact h28
  have := case2_plus P M (fun ω => -R ω) hM hR.neg κ hC hind' hneg h28' h29' hF
  have hCt : Ctwo P M (fun ω => -R ω) κ = Ctwo P M R κ := by
    unfold Ctwo; rw [tailDiffAbs_neg]
  rw [hCt] at this
  refine this.congr (fun t => ?_)
  congr 2
  ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith

/-! ### Case 2b: `M ≤ 0` a.s., where `η = B ∗ B` -/

/-- the centred lattice `lℤ` -/
def latt (l : ℝ) : Set ℝ := Set.range (fun n : ℤ => (n : ℝ) * l)

lemma latt_meas (l : ℝ) : MeasurableSet (latt l) := (Set.countable_range _).measurableSet

lemma latt_add {l a b : ℝ} (ha : a ∈ latt l) (hb : b ∈ latt l) : a + b ∈ latt l := by
  obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
  exact ⟨m + n, by push_cast; ring⟩

lemma latt_sub {l a b : ℝ} (ha : a ∈ latt l) (hb : b ∈ latt l) : a - b ∈ latt l := by
  obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
  exact ⟨m - n, by push_cast; ring⟩

lemma conv_apply_lintegral (B : Measure ℝ) [SFinite B] (S : Set ℝ) (hS : MeasurableSet S) :
    (B ∗ B) S = ∫⁻ x, B {y | x + y ∈ S} ∂B := by
  unfold Measure.conv
  rw [Measure.map_apply measurable_add hS, Measure.prod_apply (measurable_add hS)]
  rfl

/-- if `B ∗ B` lives on `lℤ` then `B` lives on `(l/2)ℤ` -/
lemma conv_self_arith (B : Measure ℝ) [IsProbabilityMeasure B] (l : ℝ)
    (h : (B ∗ B) (latt l)ᶜ = 0) : B (latt (l / 2))ᶜ = 0 := by
  have hLc := (latt_meas l).compl
  rw [conv_apply_lintegral B _ hLc] at h
  have hmeas : Measurable (fun x => B {y | x + y ∈ (latt l)ᶜ}) :=
    measurable_measure_prodMk_left (measurable_add hLc)
  rw [lintegral_eq_zero_iff hmeas] at h
  have : (ae B).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero B)
  obtain ⟨x₀, hx₀⟩ := h.exists
  simp only [Pi.zero_apply] at hx₀
  -- `B`-a.e. `y` has `x₀ + y ∈ lℤ`
  have hae : ∀ᵐ y ∂B, x₀ + y ∈ latt l := by
    rw [ae_iff]; simpa using hx₀
  -- `2 x₀ ∈ lℤ`
  have h2 : x₀ + x₀ ∈ latt l := by
    by_contra hcon
    have hL := (latt_meas l)
    have hzero : (B ∗ B) (latt l) = 0 := by
      rw [conv_apply_lintegral B _ hL]
      have hmeasL : Measurable (fun x => B {y | x + y ∈ latt l}) :=
        measurable_measure_prodMk_left (measurable_add hL)
      rw [lintegral_eq_zero_iff hmeasL]
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply]
      refine measure_mono_null (fun y hy => ?_) hx₀
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hy ⊢
      intro hy0
      apply hcon
      have := latt_sub (latt_add hx hy0) hy
      have e : x₀ + x + (x₀ + y) - (x + y) = x₀ + x₀ := by ring
      rwa [e] at this
    have h1 : (B ∗ B) Set.univ = 0 := by
      rw [← Set.union_compl_self (latt l)]
      exact measure_union_null hzero (by rw [conv_apply_lintegral B _ hLc]; exact
        (lintegral_eq_zero_iff hmeas).mpr h)
    simp at h1
  obtain ⟨m, hm⟩ := h2
  refine measure_mono_null (fun y hy => ?_) hx₀
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hy ⊢
  intro hy0
  apply hy
  obtain ⟨n, hn⟩ := hy0
  refine ⟨2 * n - m, ?_⟩
  push_cast
  linear_combination hn - hm / 2



lemma tiltOn_null (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (hs : μ s = 0) : tiltOn κ μ s = 0 := by
  unfold tiltOn
  rw [Measure.restrict_eq_zero.mpr hs]
  simp

lemma etaCase2_2b (κ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (hC : CramerConditions κ μ)
    (h0 : μ (Set.Ioi 0) = 0) :
    etaCase2 κ μ = tiltOn κ μ (Set.Iio 0) ∗ tiltOn κ μ (Set.Iio 0) := by
  rw [etaCase2_eq κ μ hC, tiltOn_null κ μ _ h0, zero_add]
  ext S hS
  rw [Measure.sum_apply _ hS, tsum_eq_single 0]
  · simp only [convPow]; rw [Measure.conv_dirac_zero]
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [convPow, Measure.zero_conv, Measure.conv_zero, Measure.coe_zero, Pi.zero_apply]

lemma facts_2b (κ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hC : CramerConditions κ μ)
    (hint2 : Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) μ) (h0 : μ (Set.Ioi 0) = 0) :
    EtaFacts κ μ := by
  set B := tiltOn κ μ (Set.Iio 0) with hBdef
  have hBu : B Set.univ = 1 := by
    rw [hBdef, ← qMinus_eq]
    have := pq_sum κ μ hC
    rw [pPlus_eq, tiltOn_null κ μ _ h0] at this
    simpa using this
  have : IsProbabilityMeasure B := ⟨hBu⟩
  have hlt : ∀ᵐ y ∂((μ.restrict (Set.Iio 0)).map (fun x => Real.log |x|)),
      ENNReal.ofReal (Real.exp (κ * y)) < ∞ :=
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  have hsm : AEStronglyMeasurable (fun y : ℝ => (ENNReal.ofReal (Real.exp (κ * y))).toReal • y)
      ((μ.restrict (Set.Iio 0)).map (fun x => Real.log |x|)) :=
    ((meas_expden κ).ennreal_toReal.smul measurable_id).aestronglyMeasurable
  have hae : ∀ᵐ x ∂(μ.restrict (Set.Iio 0)), |x| ^ κ * Real.log |x| =
      ((fun y : ℝ => (ENNReal.ofReal (Real.exp (κ * y))).toReal • y) ∘
        (fun x => Real.log |x|)) x := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    simp only [Function.comp, smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      exp_kappa_log_abs κ x (ne_of_lt hx), ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg x) κ)]
  have hBi : Integrable (fun y : ℝ => y) B := by
    rw [hBdef]; unfold tiltOn
    rw [integrable_withDensity_iff_integrable_smul' (meas_expden κ) hlt,
      integrable_map_measure hsm meas_logabs.aemeasurable]
    exact (hint2.integrableOn (s := Set.Iio 0)).congr hae
  have hBmean : ∫ y, y ∂B = cramerMean κ μ := by
    rw [hBdef]; unfold tiltOn cramerMean
    rw [integral_withDensity_eq_integral_toReal_smul (meas_expden κ) hlt,
      integral_map meas_logabs.aemeasurable hsm]
    have hnot : ∀ᵐ x ∂μ, x ∉ Set.Ioi 0 := by
      rw [ae_iff]
      have e : {a : ℝ | ¬a ∉ Set.Ioi 0} = Set.Ioi 0 := by ext; simp
      rw [e]; exact h0
    have hcond : ∀ᵐ x ∂μ, x ∉ Set.Iio 0 → |x| ^ κ * Real.log |x| = 0 := by
      filter_upwards [hnot] with x hx1 hx2
      simp only [Set.mem_Ioi, not_lt, Set.mem_Iio] at hx1 hx2
      have : x = 0 := le_antisymm hx1 hx2
      subst this
      simp [Real.zero_rpow hC.pos.ne']
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (μ := μ) (s := Set.Iio 0) hcond]
    exact (integral_congr_ae hae).symm
  unfold EtaFacts
  rw [etaCase2_2b κ μ hC h0, ← hBdef]
  have hconv : B ∗ B = (B.prod B).map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  have hIp : Integrable (fun p : ℝ × ℝ => p.1 + p.2) (B.prod B) :=
    (hBi.comp_fst B).add (hBi.comp_snd B)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [hconv, integrable_map_measure measurable_id'.aestronglyMeasurable measurable_add.aemeasurable]
    exact hIp
  · rw [hconv, integral_map measurable_add.aemeasurable measurable_id'.aestronglyMeasurable]
    show ∫ p : ℝ × ℝ, p.1 + p.2 ∂(B.prod B) = _
    rw [integral_add (hBi.comp_fst B) (hBi.comp_snd B), integral_fun_fst (fun y : ℝ => y),
      integral_fun_snd (fun y : ℝ => y), probReal_univ, hBmean]
    simp only [one_smul]; ring
  · rintro ⟨l, hl, hz⟩
    apply hC.nonarithmetic
    refine ⟨l / 2, by linarith, ?_⟩
    have hB2 : B (latt (l / 2))ᶜ = 0 := conv_self_arith B l hz
    have hSm : MeasurableSet (latt (l / 2))ᶜ := (latt_meas _).compl
    -- transfer the null set from `B` to the conditional law
    have hT : μ ((fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ∩ Set.Iio 0) = 0 := by
      rw [hBdef] at hB2; unfold tiltOn at hB2
      rw [withDensity_apply_eq_zero' (meas_expden κ).aemeasurable] at hB2
      have hall : {x : ℝ | ENNReal.ofReal (Real.exp (κ * x)) ≠ 0} = Set.univ := by
        ext x; simp [Real.exp_pos]
      rw [hall, Set.univ_inter, Measure.map_apply meas_logabs hSm,
        Measure.restrict_apply (meas_logabs hSm)] at hB2
      exact hB2
    have hne : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
    show ((μ[|{x : ℝ | x ≠ 0}]).map (fun x => Real.log |x|)) (latt (l / 2))ᶜ = 0
    rw [Measure.map_apply meas_logabs hSm, ProbabilityTheory.cond_apply hne]
    have hsub : {x : ℝ | x ≠ 0} ∩ (fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ⊆
        ((fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ∩ Set.Iio 0) ∪ Set.Ioi 0 := by
      intro x ⟨hx0, hx⟩
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    rw [measure_mono_null hsub (measure_union_null hT h0), mul_zero]

end GoldieRenewal.Implicit.Red

open MeasureTheory ProbabilityTheory Filter Topology in
open GoldieRenewal.Implicit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P) :
    ((∀ᵐ ω ∂P, 0 ≤ M ω) →
        (TailCondPlus P M R κ →
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Cplus P M R κ))) ∧
        (TailCondMinus P M R κ →
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Cminus P M R κ)))) ∧
      (0 < P {ω | M ω < 0} → TailCondPlus P M R κ → TailCondMinus P M R κ →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 (Ctwo P M R κ)) ∧
          Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop (𝓝 (Ctwo P M R κ))) := by
  refine ⟨fun hnn => ⟨fun h28 => Red.case1_plus P M R hM hR κ hC hind hnn h28,
      fun h29 => Red.case1_minus P M R hM hR κ hC hind hnn h29⟩, fun hneg h28 h29 => ?_⟩
  have hF : Red.EtaFacts κ (P.map M) := by
    have : IsProbabilityMeasure (P.map M) := Measure.isProbabilityMeasure_map hM.aemeasurable
    by_cases hpos : 0 < P {ω | 0 < M ω}
    · exact eq_9_12_9_13 P M hM κ hC hpos hneg
    · have h0 : (P.map M) (Set.Ioi 0) = 0 := by
        rw [Measure.map_apply hM measurableSet_Ioi]
        exact le_antisymm (not_lt.mp hpos) zero_le
      exact Red.facts_2b κ (P.map M) hC (lemma_2_2 P M hM κ hC).2.1 h0
  exact ⟨Red.case2_plus P M R hM hR κ hC hind hneg h28 h29 hF,
    Red.case2_minus P M R hM hR κ hC hind hneg h28 h29 hF⟩
