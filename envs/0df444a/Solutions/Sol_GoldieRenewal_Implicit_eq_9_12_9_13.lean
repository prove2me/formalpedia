-- Prove2me | solution 1 for GoldieRenewal.Implicit.eq_9_12_9_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T02:15:46.99745+00:00
-- url     : https://prove2.me/submissions/5364a3a4-9b7a-4719-961f-d991ce62f31b

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GoldieRenewal.Implicit.E2

/-! ### Tilted pieces `A = P̃(M>0, log|M| ∈ ·)`, `B = P̃(M<0, log|M| ∈ ·)` -/

noncomputable def tiltOn (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) : Measure ℝ :=
  ((μ.restrict s).map (fun x => Real.log |x|)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (κ * u)))

lemma meas_logabs : Measurable (fun x : ℝ => Real.log |x|) :=
  Real.measurable_log.comp continuous_abs.measurable

lemma meas_expden (κ : ℝ) : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (κ * u))) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

lemma meas_rpow_abs (κ : ℝ) : Measurable (fun x : ℝ => |x| ^ κ) :=
  (continuous_abs.measurable).pow_const κ

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

lemma convPow_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ] : ∀ k, IsFiniteMeasure (convPow ρ k)
  | 0 => by simp only [convPow]; infer_instance
  | k + 1 => by
    have := convPow_finite ρ k
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

/-! ### Masses via `Lc 0` -/

noncomputable def Lc (c : ℝ) (ρ : Measure ℝ) : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (Real.exp (c * y)) ∂ρ

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

lemma conv_univ (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    (ρ ∗ σ) Set.univ = ρ Set.univ * σ Set.univ := by
  rw [← Lc_zero_eq_univ, Lc_conv, Lc_zero_eq_univ, Lc_zero_eq_univ]

lemma conv_real_univ (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    (ρ ∗ σ).real Set.univ = ρ.real Set.univ * σ.real Set.univ := by
  simp only [measureReal_def, conv_univ, ENNReal.toReal_mul]

lemma convPow_real_univ (ρ : Measure ℝ) [SFinite ρ] (k : ℕ) :
    (convPow ρ k).real Set.univ = ρ.real Set.univ ^ k := by
  simp only [measureReal_def, ← Lc_zero_eq_univ, Lc_convPow, ENNReal.toReal_pow]

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

lemma tilt_ne_zero (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hs0 : s ⊆ {x | x ≠ 0}) (hpos : 0 < μ s) :
    ∫⁻ x in s, ENNReal.ofReal (|x| ^ κ) ∂μ ≠ 0 := by
  intro h
  rw [lintegral_eq_zero_iff ((continuous_abs.measurable.pow_const κ).ennreal_ofReal)] at h
  have h2 : (μ.restrict s) {x | ENNReal.ofReal (|x| ^ κ) ≠ 0} = 0 := by
    have := h
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  rw [Measure.restrict_apply' hs] at h2
  have h3 : {x : ℝ | ENNReal.ofReal (|x| ^ κ) ≠ 0} ∩ s = s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    intro hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (abs_pos.mpr (hs0 hx)) κ
  rw [h3] at h2
  exact (ne_of_gt hpos) h2

/-! ### First moments -/

lemma key_ineq (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    |x| ^ κ - 1 ≤ κ * (|x| ^ κ * Real.log |x|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hκ.ne']
  · have hy : 0 < |x| ^ κ := Real.rpow_pos_of_pos (abs_pos.2 hx) κ
    have hl : Real.log (|x| ^ κ) = κ * Real.log |x| := Real.log_rpow (abs_pos.2 hx) κ
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
    rw [Real.log_inv, hl] at h
    have h2 := mul_le_mul_of_nonneg_left h hy.le
    rw [mul_sub, mul_inv_cancel₀ hy.ne', mul_one] at h2
    nlinarith

lemma abs_phi_le (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    |x| ^ κ * abs (Real.log |x|) ≤ |x| ^ κ * max (Real.log |x|) 0 + 1 / κ := by
  have hy : 0 ≤ |x| ^ κ := Real.rpow_nonneg (abs_nonneg x) κ
  have hk : 0 < 1 / κ := by positivity
  rcases le_or_gt 0 (Real.log |x|) with h | h
  · rw [abs_of_nonneg h, max_eq_left h]; linarith
  · rw [abs_of_neg h, max_eq_right h.le, mul_zero, zero_add]
    have := key_ineq κ hκ x
    have h3 : |x| ^ κ * -Real.log |x| * κ ≤ 1 := by nlinarith
    rw [le_div_iff₀ hκ]; exact h3

section Moments
variable (κ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma lintegral_abs_phi_lt (hC : CramerConditions κ μ) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) ∂μ < ∞ := by
  calc ∫⁻ x, ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) + ENNReal.ofReal (1 / κ)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (by
          have := Real.rpow_nonneg (abs_nonneg x) κ; positivity) (by have := hC.pos; positivity)]
        exact ENNReal.ofReal_le_ofReal (abs_phi_le κ hC.pos x)
    _ = ∫⁻ x, ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) ∂μ + ENNReal.ofReal (1 / κ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hC.moment_log_finite, ENNReal.ofReal_lt_top⟩

lemma integrable_phi (hC : CramerConditions κ μ) :
    Integrable (fun x => |x| ^ κ * Real.log |x|) μ := by
  refine ⟨((meas_rpow_abs κ).mul meas_logabs).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ x : ℝ, ‖|x| ^ κ * Real.log |x|‖ₑ = ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) κ)]
  simp only [this]
  exact lintegral_abs_phi_lt κ μ hC

lemma tilt_integrable (hC : CramerConditions κ μ) (s : Set ℝ) :
    Integrable (fun y : ℝ => y) (tiltOn κ μ s) := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp only [Real.enorm_eq_ofReal_abs]
  rw [lintegral_tiltOn κ μ s (fun y => ENNReal.ofReal |y|)
    (ENNReal.measurable_ofReal.comp continuous_abs.measurable)]
  refine lt_of_le_of_lt (le_trans (setLIntegral_le_lintegral s _) (lintegral_mono fun x => ?_))
    (lintegral_abs_phi_lt κ μ hC)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [exp_kappa_log_abs κ x hx, ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ)]

lemma tilt_mean (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ {x | x ≠ 0}) :
    ∫ y, y ∂(tiltOn κ μ s) = ∫ x in s, |x| ^ κ * Real.log |x| ∂μ := by
  have hlt : ∀ᵐ y ∂((μ.restrict s).map (fun x => Real.log |x|)),
      ENNReal.ofReal (Real.exp (κ * y)) < ∞ :=
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  have hsm : AEStronglyMeasurable (fun y : ℝ => (ENNReal.ofReal (Real.exp (κ * y))).toReal • y)
      ((μ.restrict s).map (fun x => Real.log |x|)) :=
    ((meas_expden κ).ennreal_toReal.smul measurable_id).aestronglyMeasurable
  have hae : ∀ x, x ∈ s → |x| ^ κ * Real.log |x| =
      ((fun y : ℝ => (ENNReal.ofReal (Real.exp (κ * y))).toReal • y) ∘
        (fun x => Real.log |x|)) x := by
    intro x hx
    simp only [Function.comp, smul_eq_mul, exp_kappa_log_abs κ x (hs0 hx)]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg x) κ)]
  unfold tiltOn
  rw [integral_withDensity_eq_integral_toReal_smul (meas_expden κ) hlt,
    integral_map meas_logabs.aemeasurable hsm]
  refine (integral_congr_ae ?_).symm
  filter_upwards [ae_restrict_mem hs] with x hx
  exact hae x hx

end Moments

/-! ### Generic first-moment algebra for `A + Σ_k (B∗B)∗A^k` -/

lemma conv_mean (ρ σ : Measure ℝ) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hρ : Integrable (fun y : ℝ => y) ρ) (hσ : Integrable (fun y : ℝ => y) σ) :
    Integrable (fun y : ℝ => y) (ρ ∗ σ) ∧
    ∫ y, y ∂(ρ ∗ σ) = σ.real Set.univ * ∫ y, y ∂ρ + ρ.real Set.univ * ∫ y, y ∂σ ∧
    ∫ y, |y| ∂(ρ ∗ σ) ≤ σ.real Set.univ * ∫ y, |y| ∂ρ + ρ.real Set.univ * ∫ y, |y| ∂σ := by
  have hconv : ρ ∗ σ = (ρ.prod σ).map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (ρ.prod σ) := hρ.comp_fst σ
  have h2 : Integrable (fun p : ℝ × ℝ => p.2) (ρ.prod σ) := hσ.comp_snd ρ
  have hIp : Integrable (fun p : ℝ × ℝ => p.1 + p.2) (ρ.prod σ) := h1.add h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hconv, integrable_map_measure measurable_id'.aestronglyMeasurable
      measurable_add.aemeasurable]
    exact hIp
  · rw [hconv, integral_map measurable_add.aemeasurable measurable_id'.aestronglyMeasurable]
    show ∫ p : ℝ × ℝ, p.1 + p.2 ∂(ρ.prod σ) = _
    rw [integral_add h1 h2, integral_fun_fst (fun y : ℝ => y), integral_fun_snd (fun y : ℝ => y)]
    simp only [smul_eq_mul]
  · rw [hconv, integral_map measurable_add.aemeasurable continuous_abs.aestronglyMeasurable]
    have ha : Integrable (fun p : ℝ × ℝ => |p.1|) (ρ.prod σ) := hρ.abs.comp_fst σ
    have hb : Integrable (fun p : ℝ × ℝ => |p.2|) (ρ.prod σ) := hσ.abs.comp_snd ρ
    calc ∫ p : ℝ × ℝ, |p.1 + p.2| ∂(ρ.prod σ) ≤ ∫ p : ℝ × ℝ, (|p.1| + |p.2|) ∂(ρ.prod σ) :=
          integral_mono hIp.abs (ha.add hb) (fun p => abs_add_le _ _)
      _ = _ := by
          rw [integral_add ha hb, integral_fun_fst (fun y : ℝ => |y|),
            integral_fun_snd (fun y : ℝ => |y|)]
          simp only [smul_eq_mul]

lemma convPow_mean (A : Measure ℝ) [IsFiniteMeasure A] (α : ℝ) (hαd : A.real Set.univ = α)
    (hA : Integrable (fun y : ℝ => y) A) (hα : 0 < α) : ∀ k : ℕ,
    Integrable (fun y : ℝ => y) (convPow A k) ∧
    ∫ y, y ∂(convPow A k) = k * α ^ k * ((∫ y, y ∂A) / α) ∧
    ∫ y, |y| ∂(convPow A k) ≤ k * α ^ k * ((∫ y, |y| ∂A) / α)
  | 0 => by
    simp only [convPow, Nat.cast_zero, zero_mul]
    refine ⟨integrable_dirac (by simp), by simp, by simp⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := convPow_mean A α hαd hA hα k
    have := convPow_finite A k
    obtain ⟨i1, i2, i3⟩ := conv_mean A (convPow A k) hA h1
    rw [convPow_real_univ, hαd] at i2 i3
    have hne : α ≠ 0 := hα.ne'
    simp only [convPow]
    refine ⟨i1, ?_, ?_⟩
    · rw [i2, h2]; field_simp; push_cast; ring
    · refine le_trans i3 ?_
      calc α ^ k * ∫ y, |y| ∂A + α * ∫ y, |y| ∂(convPow A k)
          ≤ α ^ k * ∫ y, |y| ∂A + α * (k * α ^ k * ((∫ y, |y| ∂A) / α)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hα.le)
        _ = _ := by field_simp; push_cast; ring

lemma summable_k (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : Summable (fun k : ℕ => (k : ℝ) * α ^ k) := by
  have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := α)
    (by rw [Real.norm_eq_abs, abs_of_pos hα]; exact hα1)
  simpa using this

lemma gen_eta (A B : Measure ℝ) [IsFiniteMeasure A] [IsFiniteMeasure B] (α β : ℝ)
    (hαd : A.real Set.univ = α) (hβd : B.real Set.univ = β)
    (hA : Integrable (fun y : ℝ => y) A) (hB : Integrable (fun y : ℝ => y) B)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) :
    Integrable (fun y : ℝ => y) (A + Measure.sum (fun k : ℕ => (B ∗ B) ∗ convPow A k)) ∧
    ∫ y, y ∂(A + Measure.sum (fun k : ℕ => (B ∗ B) ∗ convPow A k)) =
      2 * (∫ y, y ∂A + ∫ y, y ∂B) := by
  have hα1 : α < 1 := by linarith
  obtain ⟨b1, b2, b3⟩ := conv_mean B B hB hB
  rw [hβd] at b2 b3
  have hterm : ∀ k : ℕ, Integrable (fun y : ℝ => y) ((B ∗ B) ∗ convPow A k) ∧
      ∫ y, y ∂((B ∗ B) ∗ convPow A k) =
        α ^ k * (2 * β * ∫ y, y ∂B) + β ^ 2 * ((∫ y, y ∂A) / α) * (k * α ^ k) ∧
      ∫ y, |y| ∂((B ∗ B) ∗ convPow A k) ≤
        α ^ k * (2 * β * ∫ y, |y| ∂B) + β ^ 2 * ((∫ y, |y| ∂A) / α) * (k * α ^ k) := by
    intro k
    have := convPow_finite A k
    obtain ⟨h1, h2, h3⟩ := convPow_mean A α hαd hA hα k
    obtain ⟨i1, i2, i3⟩ := conv_mean (B ∗ B) (convPow A k) b1 h1
    rw [convPow_real_univ, conv_real_univ, hαd, hβd] at i2 i3
    refine ⟨i1, ?_, ?_⟩
    · rw [i2, h2, b2]; ring
    · refine le_trans i3 ?_
      have hαk : 0 ≤ α ^ k := pow_nonneg hα.le k
      have hββ : 0 ≤ β * β := mul_nonneg hβ.le hβ.le
      calc α ^ k * ∫ y, |y| ∂(B ∗ B) + β * β * ∫ y, |y| ∂(convPow A k)
          ≤ α ^ k * (β * ∫ y, |y| ∂B + β * ∫ y, |y| ∂B) +
              β * β * (k * α ^ k * ((∫ y, |y| ∂A) / α)) :=
            add_le_add (mul_le_mul_of_nonneg_left b3 hαk) (mul_le_mul_of_nonneg_left h3 hββ)
        _ = _ := by ring
  have g1 := summable_geometric_of_lt_one hα.le hα1
  have g2 := summable_k α hα hα1
  obtain ⟨c1, hc1⟩ : ∃ c, c = 2 * β * ∫ y, |y| ∂B := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = β ^ 2 * ((∫ y, |y| ∂A) / α) := ⟨_, rfl⟩
  have hg : Summable (fun k : ℕ => α ^ k * c1 + c2 * ((k : ℝ) * α ^ k)) :=
    (g1.mul_right c1).add (g2.mul_left c2)
  have hs2 : Summable (fun k : ℕ => ∫ y, ‖y‖ ∂((B ∗ B) ∗ convPow A k)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun y => norm_nonneg _))
      (fun k => ?_) hg
    have h := (hterm k).2.2
    rw [← hc1, ← hc2] at h
    simp only [Real.norm_eq_abs]
    exact h
  have hsum : Integrable (fun y : ℝ => y) (Measure.sum (fun k : ℕ => (B ∗ B) ∗ convPow A k)) :=
    integrable_sum_measure (fun k => (hterm k).1) hs2
  refine ⟨hA.add_measure hsum, ?_⟩
  rw [integral_add_measure hA hsum, integral_sum_measure hsum]
  have e : ∀ k : ℕ, ∫ y, y ∂((B ∗ B) ∗ convPow A k) =
      α ^ k * (2 * β * ∫ y, y ∂B) + β ^ 2 * ((∫ y, y ∂A) / α) * (k * α ^ k) :=
    fun k => (hterm k).2.1
  simp only [e]
  rw [Summable.tsum_add (g1.mul_right (2 * β * ∫ y, y ∂B)) (g2.mul_left (β ^ 2 * ((∫ y, y ∂A) / α))), tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one hα.le hα1,
    tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_pos hα]; exact hα1)]
  have hb : 1 - α = β := by linarith
  rw [hb]
  have hne : α ≠ 0 := hα.ne'
  have hne' : β ≠ 0 := hβ.ne'
  field_simp
  ring

/-! ### Lattices -/

def latt (l : ℝ) : Set ℝ := Set.range (fun n : ℤ => (n : ℝ) * l)

lemma latt_meas (l : ℝ) : MeasurableSet (latt l) := (Set.countable_range _).measurableSet

lemma latt_add {l a b : ℝ} (ha : a ∈ latt l) (hb : b ∈ latt l) : a + b ∈ latt l := by
  obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
  exact ⟨m + n, by push_cast; ring⟩

lemma latt_sub {l a b : ℝ} (ha : a ∈ latt l) (hb : b ∈ latt l) : a - b ∈ latt l := by
  obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
  exact ⟨m - n, by push_cast; ring⟩

lemma latt_half (l : ℝ) : latt l ⊆ latt (l / 2) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨2 * n, by push_cast; ring⟩

lemma conv_apply_lintegral (B : Measure ℝ) [SFinite B] (S : Set ℝ) (hS : MeasurableSet S) :
    (B ∗ B) S = ∫⁻ x, B {y | x + y ∈ S} ∂B := by
  unfold Measure.conv
  rw [Measure.map_apply measurable_add hS, Measure.prod_apply (measurable_add hS)]
  rfl

/-- if `B ∗ B` lives on `lℤ` then `B` lives on `(l/2)ℤ` -/
lemma conv_self_arith (B : Measure ℝ) [IsFiniteMeasure B] (hB : B ≠ 0) (l : ℝ)
    (h : (B ∗ B) (latt l)ᶜ = 0) : B (latt (l / 2))ᶜ = 0 := by
  have hLc := (latt_meas l).compl
  rw [conv_apply_lintegral B _ hLc] at h
  have hmeas : Measurable (fun x => B {y | x + y ∈ (latt l)ᶜ}) :=
    measurable_measure_prodMk_left (measurable_add hLc)
  rw [lintegral_eq_zero_iff hmeas] at h
  have : (ae B).NeBot := ae_neBot.mpr hB
  obtain ⟨x₀, hx₀⟩ := h.exists
  simp only [Pi.zero_apply] at hx₀
  have hae : ∀ᵐ y ∂B, x₀ + y ∈ latt l := by
    rw [ae_iff]; simpa using hx₀
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
    rw [conv_univ, mul_self_eq_zero, Measure.measure_univ_eq_zero] at h1
    exact hB h1
  obtain ⟨m, hm⟩ := h2
  refine measure_mono_null (fun y hy => ?_) hx₀
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hy ⊢
  intro hy0
  apply hy
  obtain ⟨n, hn⟩ := hy0
  refine ⟨2 * n - m, ?_⟩
  push_cast
  linear_combination hn - hm / 2

/-! ### Assembly -/

section Main
variable (κ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma tilt_finite (hC : CramerConditions κ μ) (s : Set ℝ) (hs : MeasurableSet s)
    (hs0 : s ⊆ {x | x ≠ 0}) : IsFiniteMeasure (tiltOn κ μ s) := by
  constructor
  rw [tiltOn_univ κ μ s hs hs0]
  exact lt_of_le_of_lt (le_trans (setLIntegral_le_lintegral _ _) hC.moment_eq_one.le)
    ENNReal.one_lt_top

lemma cramerMean_split (hC : CramerConditions κ μ) :
    cramerMean κ μ = ∫ x in Set.Ioi 0, |x| ^ κ * Real.log |x| ∂μ +
      ∫ x in Set.Iio 0, |x| ^ κ * Real.log |x| ∂μ := by
  have hint := integrable_phi κ μ hC
  have hd : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]; intro x h1 h2; exact lt_asymm (Set.mem_Ioi.mp h1) (Set.mem_Iio.mp h2)
  rw [← setIntegral_union hd measurableSet_Iio hint.integrableOn hint.integrableOn]
  unfold cramerMean
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  have hx0 : x = 0 := by
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, not_or, not_lt] at hx
    exact le_antisymm hx.1 hx.2
  subst hx0; simp

lemma tilt_null (s S : Set ℝ) (hS : MeasurableSet S) (h : tiltOn κ μ s S = 0) :
    μ ((fun x => Real.log |x|) ⁻¹' S ∩ s) = 0 := by
  unfold tiltOn at h
  rw [withDensity_apply_eq_zero' (meas_expden κ).aemeasurable] at h
  have hall : {x : ℝ | ENNReal.ofReal (Real.exp (κ * x)) ≠ 0} = Set.univ := by
    ext x; simp [Real.exp_pos]
  rw [hall, Set.univ_inter, Measure.map_apply meas_logabs hS,
    Measure.restrict_apply (meas_logabs hS)] at h
  exact h

theorem main (hC : CramerConditions κ μ) (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    IsProbabilityMeasure (etaCase2 κ μ) ∧ Integrable (fun y : ℝ => y) (etaCase2 κ μ) ∧
      ∫ y, y ∂(etaCase2 κ μ) = 2 * cramerMean κ μ ∧ ¬ IsArithmetic (etaCase2 κ μ) := by
  obtain ⟨A, hAdef⟩ : ∃ A, A = tiltOn κ μ (Set.Ioi 0) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = tiltOn κ μ (Set.Iio 0) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure A := by rw [hAdef]; exact tilt_finite κ μ hC _ measurableSet_Ioi Ioi_ne
  haveI : IsFiniteMeasure B := by rw [hBdef]; exact tilt_finite κ μ hC _ measurableSet_Iio Iio_ne
  have hpq := pq_sum κ μ hC
  rw [pPlus_eq, qMinus_eq, ← hAdef, ← hBdef] at hpq
  have hp0 : A Set.univ ≠ 0 := by
    rw [hAdef, tiltOn_univ κ μ _ measurableSet_Ioi Ioi_ne]
    exact tilt_ne_zero κ μ _ measurableSet_Ioi Ioi_ne hpos
  have hq0 : B Set.univ ≠ 0 := by
    rw [hBdef, tiltOn_univ κ μ _ measurableSet_Iio Iio_ne]
    exact tilt_ne_zero κ μ _ measurableSet_Iio Iio_ne hneg
  have hpt : A Set.univ ≠ ⊤ := measure_ne_top A _
  have hqt : B Set.univ ≠ ⊤ := measure_ne_top B _
  have hα : 0 < A.real Set.univ := ENNReal.toReal_pos hp0 hpt
  have hβ : 0 < B.real Set.univ := ENNReal.toReal_pos hq0 hqt
  have hαβ : A.real Set.univ + B.real Set.univ = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add hpt hqt, hpq, ENNReal.toReal_one]
  have hη := etaCase2_eq κ μ hC
  rw [← hAdef, ← hBdef] at hη
  have hAi : Integrable (fun y : ℝ => y) A := by rw [hAdef]; exact tilt_integrable κ μ hC _
  have hBi : Integrable (fun y : ℝ => y) B := by rw [hBdef]; exact tilt_integrable κ μ hC _
  obtain ⟨hI, hmean⟩ := gen_eta A B _ _ rfl rfl hAi hBi hα hβ hαβ
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [hη, ← Lc_zero_eq_univ, Lc_eta, Lc_zero_eq_univ, Lc_zero_eq_univ]
    have h1 : 1 - A Set.univ = B Set.univ := by rw [← hpq]; exact ENNReal.add_sub_cancel_left hpt
    rw [h1, sq, mul_assoc, ENNReal.mul_inv_cancel hq0 hqt, mul_one, hpq]
  · rw [hη]; exact hI
  · rw [hη, hmean, hAdef, hBdef, tilt_mean κ μ _ measurableSet_Ioi Ioi_ne,
      tilt_mean κ μ _ measurableSet_Iio Iio_ne, cramerMean_split κ μ hC]
  · rintro ⟨l, hl, hz⟩
    have hz' : etaCase2 κ μ (latt l)ᶜ = 0 := hz
    have hSm : MeasurableSet (latt l)ᶜ := (latt_meas l).compl
    rw [hη, Measure.add_apply, add_eq_zero, Measure.sum_apply _ hSm] at hz'
    obtain ⟨hA0, hS0⟩ := hz'
    have hBB : ((B ∗ B) ∗ convPow A 0) (latt l)ᶜ = 0 := ENNReal.tsum_eq_zero.mp hS0 0
    simp only [convPow] at hBB
    rw [Measure.conv_dirac_zero] at hBB
    have hBne : B ≠ 0 := fun h => hq0 (by rw [h]; simp)
    have hB2 := conv_self_arith B hBne l hBB
    have hA2 : A (latt (l / 2))ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr (latt_half l)) hA0
    have hSm2 : MeasurableSet (latt (l / 2))ᶜ := (latt_meas _).compl
    rw [hAdef] at hA2
    rw [hBdef] at hB2
    have hT1 := tilt_null κ μ _ _ hSm2 hA2
    have hT2 := tilt_null κ μ _ _ hSm2 hB2
    apply hC.nonarithmetic
    refine ⟨l / 2, by linarith, ?_⟩
    have hne : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
    show ((μ[|{x : ℝ | x ≠ 0}]).map (fun x => Real.log |x|)) (latt (l / 2))ᶜ = 0
    rw [Measure.map_apply meas_logabs hSm2, ProbabilityTheory.cond_apply hne]
    have hsub : {x : ℝ | x ≠ 0} ∩ (fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ⊆
        ((fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ∩ Set.Iio 0) ∪
          ((fun x => Real.log |x|) ⁻¹' (latt (l / 2))ᶜ ∩ Set.Ioi 0) := by
      intro x ⟨hx0, hx⟩
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    rw [measure_mono_null hsub (measure_union_null hT2 hT1), mul_zero]

end Main

end GoldieRenewal.Implicit.E2

open MeasureTheory ProbabilityTheory GoldieRenewal.Implicit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ : ℝ) (hC : CramerConditions κ (P.map M))
    (hpos : 0 < P {ω | 0 < M ω}) (hneg : 0 < P {ω | M ω < 0}) :
    IsProbabilityMeasure (etaCase2 κ (P.map M)) ∧
      Integrable (fun y : ℝ => y) (etaCase2 κ (P.map M)) ∧
      ∫ y, y ∂(etaCase2 κ (P.map M)) = 2 * cramerMean κ (P.map M) ∧
      ¬ IsArithmetic (etaCase2 κ (P.map M)) := by
  haveI : IsProbabilityMeasure (P.map M) := Measure.isProbabilityMeasure_map hM.aemeasurable
  refine E2.main κ (P.map M) hC ?_ ?_
  · rw [Measure.map_apply hM measurableSet_Ioi]; exact hpos
  · rw [Measure.map_apply hM measurableSet_Iio]; exact hneg
