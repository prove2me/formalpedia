-- Prove2me | solution 1 for GoldieRenewal.Rates.contour_convolution_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:55:12.401574+00:00
-- url     : https://prove2.me/submissions/23c002be-7dcd-4a24-98e7-e5eeab4f42e6

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory Complex
open GoldieRenewal.Rates

lemma norm_exp_seg_aux (y s u β : ℝ) (hy1 : -β ≤ y) (hy2 : y ≤ 0) (γ : ℂ) (hγ : γ.im = y) :
    ‖Complex.exp (-(I * γ * ((s - u : ℝ) : ℂ)))‖ ≤
      Real.exp (β * |s|) * (1 + Real.exp (β * u)) := by
  rw [Complex.norm_exp]
  have hre : (-(I * γ * ((s - u : ℝ) : ℂ))).re = y * (s - u) := by
    simp [Complex.mul_re, hγ]
  rw [hre]
  have hβ : 0 ≤ β := by linarith
  rw [mul_add, mul_one, ← Real.exp_add]
  rcases le_total 0 u with hu | hu
  · have : y * (s - u) ≤ β * |s| + β * u := by
      have h1 : y * s ≤ β * |s| := by
        have := neg_abs_le s
        have := le_abs_self s
        nlinarith [abs_nonneg s]
      nlinarith
    calc Real.exp (y * (s - u)) ≤ Real.exp (β * |s| + β * u) := Real.exp_le_exp.2 this
      _ ≤ _ := by linarith [Real.exp_pos (β * |s|)]
  · have : y * (s - u) ≤ β * |s| := by
      have := neg_abs_le s
      have := le_abs_self s
      nlinarith [abs_nonneg s]
    calc Real.exp (y * (s - u)) ≤ Real.exp (β * |s|) := Real.exp_le_exp.2 this
      _ ≤ _ := by linarith [Real.exp_pos (β * |s| + β * u)]

lemma seg_swap_aux (β : ℝ) (hβ : 0 ≤ β) (g : ℝ → ℝ) (hgm : Measurable g) (hg1 : Integrable g)
    (hg2 : Integrable (fun u => g u * Real.exp (β * u)))
    (a b : ℝ) (hab : a ≤ b) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (him : ∀ x ∈ Set.Icc a b, -β ≤ (γ x).im ∧ (γ x).im ≤ 0)
    (ψ : ℝ → ℂ) (hψ : ContinuousOn ψ (Set.Icc a b)) (hψ0 : ∀ x ∈ Set.Icc a b, ψ x ≠ 0)
    (s : ℝ) :
    Integrable (fun u => (g u : ℂ) *
      ∫ x in a..b, Complex.exp (-(I * γ x * ((s - u : ℝ) : ℂ))) / ψ x) ∧
    ∫ u, (g u : ℂ) * ∫ x in a..b, Complex.exp (-(I * γ x * ((s - u : ℝ) : ℂ))) / ψ x
      = ∫ x in a..b, Complex.exp (-(I * γ x * (s : ℂ))) *
          (∫ u : ℝ, Complex.exp (I * γ x * (u : ℂ)) * (g u : ℂ)) / ψ x := by
  have hψi : ContinuousOn (fun x => (ψ x)⁻¹) (Set.Icc a b) := hψ.inv₀ hψ0
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψi
  set ν : Measure ℝ := volume.restrict (Set.Ioc a b) with hν
  set F : ℝ × ℝ → ℂ := fun p => (g p.1 : ℂ) *
    (Complex.exp (-(I * γ p.2 * ((s - p.1 : ℝ) : ℂ))) * (ψ p.2)⁻¹) with hF
  have hνfin : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hsub : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have hmeasF : AEStronglyMeasurable F ((volume : Measure ℝ).prod ν) := by
    refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ ?_)
    · exact (Complex.measurable_ofReal.comp (hgm.comp measurable_fst)).aestronglyMeasurable
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(I * γ p.2 * ((s - p.1 : ℝ) : ℂ)))).aestronglyMeasurable
    · exact AEStronglyMeasurable.comp_snd
        ((hψi.mono hsub).aestronglyMeasurable measurableSet_Ioc)
  have hbound_int : Integrable (fun p : ℝ × ℝ =>
      (C * Real.exp (β * |s|) * (|g p.1| + |g p.1 * Real.exp (β * p.1)|)) * (1 : ℝ))
      ((volume : Measure ℝ).prod ν) := by
    refine Integrable.mul_prod (f := fun u : ℝ => C * Real.exp (β * |s|) * (|g u| + |g u * Real.exp (β * u)|)) ?_ (integrable_const (μ := ν) (1 : ℝ))
    exact ((hg1.abs.add hg2.abs).const_mul _)
  have hae : ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p.2 ∈ Set.Ioc a b :=
    (Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioc)
  have hFint : Integrable F ((volume : Measure ℝ).prod ν) := by
    refine hbound_int.mono' hmeasF ?_
    filter_upwards [hae] with p hp
    have hp' := hsub hp
    obtain ⟨h1, h2⟩ := him p.2 hp'
    have hb1 := norm_exp_seg_aux (γ p.2).im s p.1 β h1 h2 (γ p.2) rfl
    have hb2 : ‖(ψ p.2)⁻¹‖ ≤ C := hC p.2 hp'
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_one]
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hb2
    have hg_abs : |g p.1| * (1 + Real.exp (β * p.1)) =
        |g p.1| + |g p.1 * Real.exp (β * p.1)| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]; ring
    calc |g p.1| * (‖Complex.exp (-(I * γ p.2 * ((s - p.1 : ℝ) : ℂ)))‖ * ‖(ψ p.2)⁻¹‖)
        ≤ |g p.1| * ((Real.exp (β * |s|) * (1 + Real.exp (β * p.1))) * C) := by
          gcongr
      _ = C * Real.exp (β * |s|) * (|g p.1| * (1 + Real.exp (β * p.1))) := by ring
      _ = _ := by rw [hg_abs]
  have hrew : ∀ u : ℝ, (g u : ℂ) *
      ∫ x in a..b, Complex.exp (-(I * γ x * ((s - u : ℝ) : ℂ))) / ψ x = ∫ x, F (u, x) ∂ν := by
    intro u
    rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
    simp only [hF, div_eq_mul_inv]
    rfl
  have hrew2 : ∀ x : ℝ, ∫ u, F (u, x) = Complex.exp (-(I * γ x * (s : ℂ))) *
      (∫ u : ℝ, Complex.exp (I * γ x * (u : ℂ)) * (g u : ℂ)) / ψ x := by
    intro x
    simp only [hF]
    rw [div_eq_mul_inv, ← integral_const_mul, ← integral_mul_const]
    congr 1
    funext u
    have : Complex.exp (-(I * γ x * ((s - u : ℝ) : ℂ))) =
        Complex.exp (-(I * γ x * (s : ℂ))) * Complex.exp (I * γ x * (u : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  refine ⟨?_, ?_⟩
  · simp only [hrew]
    exact hFint.integral_prod_left
  · simp only [hrew]
    rw [integral_integral_swap (f := fun u x => F (u, x)) hFint,
      intervalIntegral.integral_of_le hab]
    simp only [hrew2]
    rfl

lemma tail_antitone_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) : Measurable (fun t : ℝ => P.real {ω | t < Z ω}) := by
  apply Antitone.measurable
  intro a b hab
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hω ⊢
  linarith

lemma abs_diff_prob_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) : |P.real A - P.real B| ≤ 1 := by
  rw [abs_sub_le_iff]
  have h1 := measureReal_le_one (μ := P) (s := A)
  have h2 := measureReal_le_one (μ := P) (s := B)
  have h3 := measureReal_nonneg (μ := P) (s := A)
  have h4 := measureReal_nonneg (μ := P) (s := B)
  constructor <;> linarith

lemma gPos_measurable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (κ : ℝ) : Measurable (gPos P M R κ) := by
  unfold gPos
  have h1 := (tail_antitone_aux P R).comp Real.measurable_exp
  have h2 := (tail_antitone_aux P (fun ω => M ω * R ω)).comp Real.measurable_exp
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (h1.sub h2)

lemma gPos_integrable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    Integrable (gPos P M R κ) ∧ Integrable (fun u => gPos P M R κ u * Real.exp (β * u)) := by
  have hm := gPos_measurable_aux P M R κ
  have hm2 : Measurable (fun u => gPos P M R κ u * Real.exp (β * u)) :=
    hm.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  -- weighted, on Ioi 0
  have hIoi : IntegrableOn (fun u => gPos P M R κ u * Real.exp (β * u)) (Set.Ioi 0) := by
    have key := (integrableOn_comp_exp_Ioi (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) 0).2
      (by rw [Real.exp_zero]; exact h_3_7.mono_set (Set.Ioi_subset_Ioi zero_le_one))
    refine key.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, gPos]
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    have : Real.exp x * Real.exp (x * (κ + β - 1)) = Real.exp (κ * x) * Real.exp (β * x) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp x * ((P.real {ω | Real.exp x < R ω} - P.real {ω | Real.exp x < M ω * R ω}) *
          Real.exp (x * (κ + β - 1)))
        = (Real.exp x * Real.exp (x * (κ + β - 1))) *
          (P.real {ω | Real.exp x < R ω} - P.real {ω | Real.exp x < M ω * R ω}) := by ring
      _ = _ := by rw [this]; ring
  have hgabs : ∀ u, |gPos P M R κ u| ≤ Real.exp (κ * u) := by
    intro u
    unfold gPos
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (κ * u) * |_| ≤ Real.exp (κ * u) * 1 := by
          gcongr; exact abs_diff_prob_le P _ _
      _ = _ := mul_one _
  have hIic : IntegrableOn (fun u => gPos P M R κ u * Real.exp (β * u)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (by linarith : 0 < κ + β) 0).mono'
      hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |gPos P M R κ u| * Real.exp (β * u) ≤ Real.exp (κ * u) * Real.exp (β * u) := by
          gcongr; exact hgabs u
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Integrable (fun u => gPos P M R κ u * Real.exp (β * u)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.union hIoi
  have h1a : IntegrableOn (gPos P M R κ) (Set.Ioi 0) := by
    refine hIoi.norm.mono' hm.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : 1 ≤ Real.exp (β * u) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [Set.mem_Ioi.1 hu])
    nlinarith [abs_nonneg (gPos P M R κ u)]
  have h1b : IntegrableOn (gPos P M R κ) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hκ 0).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]; exact hgabs u
  refine ⟨?_, h2⟩
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact h1b.union h1a
lemma tilted_prob_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (κ : ℝ) (hκ : 0 < κ)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1) :
    IsProbabilityMeasure (tiltedLaw P M κ) := by
  constructor
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  unfold tiltedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_map (by fun_prop) (by fun_prop)]
  rw [← h_2_3]
  conv_rhs => rw [← lintegral_add_compl _ hS]
  have h2 : ∫⁻ ω in {ω | 0 < M ω}ᶜ, ENNReal.ofReal (|M ω| ^ κ) ∂P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    refine (ae_restrict_iff' hS.compl).2 (hM_nonneg.mono fun ω h hω => ?_)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
    have : M ω = 0 := le_antisymm hω h
    simp [this, Real.zero_rpow (ne_of_gt hκ)]
  rw [h2, add_zero]
  apply setLIntegral_congr_fun hS
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [abs_of_pos hω, Real.rpow_def_of_pos hω, mul_comm]

lemma tilted_exp_integrable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → ℝ) (hM : Measurable M) (κ β : ℝ)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤) :
    Integrable (fun t : ℝ => Real.exp (β * t)) (tiltedLaw P M κ) := by
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  refine ⟨(Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∫⁻ t, ‖Real.exp (β * t)‖ₑ ∂(tiltedLaw P M κ) ≤
      ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P := by
    unfold tiltedLaw
    rw [lintegral_withDensity_eq_lintegral_mul _ (by measurability) (by measurability),
      lintegral_map (by measurability) (by fun_prop)]
    refine le_trans (le_of_eq ?_)
      (setLIntegral_le_lintegral {ω | 0 < M ω} (fun ω => ENNReal.ofReal (|M ω| ^ (κ + β))))
    apply setLIntegral_congr_fun hS
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Pi.mul_apply, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos hω]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      Real.rpow_def_of_pos hω]
    congr 2; ring
  exact lt_of_le_of_lt hle h_3_3

lemma norm_exp_char_aux (θ : ℂ) (t β : ℝ) (h1 : -β ≤ θ.im) (h2 : θ.im ≤ 0) :
    ‖Complex.exp (I * θ * (t : ℂ))‖ ≤ 1 + Real.exp (β * t) := by
  rw [Complex.norm_exp]
  have hre : (I * θ * (t : ℂ)).re = -θ.im * t := by simp [Complex.mul_re]
  rw [hre]
  rcases le_total 0 t with ht | ht
  · have : -θ.im * t ≤ β * t := by nlinarith
    linarith [Real.exp_le_exp.2 this, Real.exp_pos (β * t)]
  · have : -θ.im * t ≤ 0 := by nlinarith
    have := Real.exp_le_exp.2 this
    rw [Real.exp_zero] at this
    linarith [Real.exp_pos (β * t)]

lemma charTransform_continuousOn_aux (η : Measure ℝ) [IsFiniteMeasure η] (β : ℝ)
    (hint : Integrable (fun t : ℝ => Real.exp (β * t)) η) :
    ContinuousOn (charTransform η) {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} := by
  unfold charTransform
  refine continuousOn_of_dominated (bound := fun t => 1 + Real.exp (β * t)) ?_ ?_
    ((integrable_const 1).add hint) ?_
  · intro θ _
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (I * θ * (t : ℂ))).aestronglyMeasurable
  · intro θ hθ
    exact Filter.Eventually.of_forall fun t => norm_exp_char_aux θ t β hθ.1 hθ.2
  · exact Filter.Eventually.of_forall fun t =>
      (by fun_prop : Continuous fun θ : ℂ => Complex.exp (I * θ * (t : ℂ))).continuousOn

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (z w : ℂ)
    (h_C : EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w)
    (s : ℝ) :
    ∫ u : ℝ, (gPos P M R κ u : ℂ) * cFun (tiltedLaw P M κ) z w (s - u) =
      (1 / (2 * Real.pi : ℂ)) *
        RectangleIntegral
          (fun θ : ℂ => Complex.exp (-(I * θ * (s : ℂ))) *
            fourierTransform (fun v => (gPos P M R κ v : ℂ)) θ /
              (1 - charTransform (tiltedLaw P M κ) θ)) z w := by
  set η := tiltedLaw P M κ with hη
  set g := gPos P M R κ with hg
  have : IsProbabilityMeasure η := tilted_prob_aux P M hM hM_nonneg κ hκ h_2_3
  have hgm : Measurable g := gPos_measurable_aux P M R κ
  obtain ⟨hg1, hg2⟩ := gPos_integrable_aux P M R κ β hκ hβ h_3_7
  have hcont := charTransform_continuousOn_aux η β
    (tilted_exp_integrable_aux P M hM κ β h_3_3)
  obtain ⟨hzw, hz1, hz2, hw2, hzeros⟩ := h_C
  have hzw' : z.im ≤ w.im := hz2.le
  -- no zero of 1 - η̂ on the four sides
  have hnz : ∀ θ : ℂ, z.im ≤ θ.im → θ.im ≤ w.im → z.re ≤ θ.re → θ.re ≤ w.re →
      (θ.im = z.im ∨ θ.im = w.im ∨ θ.re = z.re ∨ θ.re = w.re) →
      1 - charTransform η θ ≠ 0 := by
    intro θ h1 h2 h3 h4 hside h0
    have := hzeros θ (by linarith) (by linarith) h0
    rcases hside with h | h | h | h <;> linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have hmaps : ∀ θ : ℂ, z.im ≤ θ.im → θ.im ≤ w.im → θ ∈ {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} :=
    fun θ h1 h2 => ⟨by linarith, by linarith⟩
  -- the four sides
  have S1 := seg_swap_aux β hβ.le g hgm hg1 hg2 z.re w.re hzw.le
    (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I) (by fun_prop)
    (fun x _ => by simp; constructor <;> linarith)
    (fun x : ℝ => 1 - charTransform η ((x : ℂ) + (z.im : ℂ) * I))
    (continuousOn_const.sub (hcont.comp (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) + (z.im : ℂ) * I).continuousOn (fun x _ => hmaps _ (by simp) (by simp; linarith))))
    (fun x hx => hnz _ (by simp) (by simp; linarith) (by simp; exact hx.1) (by simp; exact hx.2)
      (Or.inl (by simp))) s
  have S2 := seg_swap_aux β hβ.le g hgm hg1 hg2 z.re w.re hzw.le
    (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I) (by fun_prop)
    (fun x _ => by simp; constructor <;> linarith)
    (fun x : ℝ => 1 - charTransform η ((x : ℂ) + (w.im : ℂ) * I))
    (continuousOn_const.sub (hcont.comp (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) + (w.im : ℂ) * I).continuousOn (fun x _ => hmaps _ (by simp; linarith) (by simp))))
    (fun x hx => hnz _ (by simp; linarith) (by simp) (by simp; exact hx.1) (by simp; exact hx.2)
      (Or.inr (Or.inl (by simp)))) s
  have S3 := seg_swap_aux β hβ.le g hgm hg1 hg2 z.im w.im hzw'
    (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I) (by fun_prop)
    (fun y hy => by simp; constructor <;> linarith [hy.1, hy.2])
    (fun y : ℝ => 1 - charTransform η ((w.re : ℂ) + (y : ℂ) * I))
    (continuousOn_const.sub (hcont.comp (by fun_prop : Continuous fun y : ℝ =>
      (w.re : ℂ) + (y : ℂ) * I).continuousOn
        (fun y hy => hmaps _ (by simp; exact hy.1) (by simp; exact hy.2))))
    (fun y hy => hnz _ (by simp; exact hy.1) (by simp; exact hy.2) (by simp; linarith) (by simp)
      (Or.inr (Or.inr (Or.inr (by simp))))) s
  have S4 := seg_swap_aux β hβ.le g hgm hg1 hg2 z.im w.im hzw'
    (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I) (by fun_prop)
    (fun y hy => by simp; constructor <;> linarith [hy.1, hy.2])
    (fun y : ℝ => 1 - charTransform η ((z.re : ℂ) + (y : ℂ) * I))
    (continuousOn_const.sub (hcont.comp (by fun_prop : Continuous fun y : ℝ =>
      (z.re : ℂ) + (y : ℂ) * I).continuousOn
        (fun y hy => hmaps _ (by simp; exact hy.1) (by simp; exact hy.2))))
    (fun y hy => hnz _ (by simp; exact hy.1) (by simp; exact hy.2) (by simp) (by simp; linarith)
      (Or.inr (Or.inr (Or.inl (by simp))))) s
  beta_reduce at S1 S2 S3 S4
  obtain ⟨I1, E1⟩ := S1
  obtain ⟨I2, E2⟩ := S2
  obtain ⟨I3, E3⟩ := S3
  obtain ⟨I4, E4⟩ := S4
  have hpt : ∀ u : ℝ, (g u : ℂ) * cFun η z w (s - u) = (1 / (2 * Real.pi : ℂ)) *
      ((g u : ℂ) * (∫ x in z.re..w.re, Complex.exp (-(I * ((x : ℂ) + (z.im : ℂ) * I) *
          ((s - u : ℝ) : ℂ))) / (1 - charTransform η ((x : ℂ) + (z.im : ℂ) * I))) -
        (g u : ℂ) * (∫ x in z.re..w.re, Complex.exp (-(I * ((x : ℂ) + (w.im : ℂ) * I) *
          ((s - u : ℝ) : ℂ))) / (1 - charTransform η ((x : ℂ) + (w.im : ℂ) * I))) +
        I * ((g u : ℂ) * (∫ y in z.im..w.im, Complex.exp (-(I * ((w.re : ℂ) + (y : ℂ) * I) *
          ((s - u : ℝ) : ℂ))) / (1 - charTransform η ((w.re : ℂ) + (y : ℂ) * I)))) -
        I * ((g u : ℂ) * (∫ y in z.im..w.im, Complex.exp (-(I * ((z.re : ℂ) + (y : ℂ) * I) *
          ((s - u : ℝ) : ℂ))) / (1 - charTransform η ((z.re : ℂ) + (y : ℂ) * I))))) := by
    intro u
    simp only [cFun, RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
    ring
  simp only [hpt]
  have e1 := integral_sub ((I1.sub I2).add (I3.const_mul I)) (I4.const_mul I)
  have e2 := integral_add (I1.sub I2) (I3.const_mul I)
  have e3 := integral_sub I1 I2
  simp only [Pi.add_apply, Pi.sub_apply] at e1 e2 e3
  rw [integral_const_mul, e1, e2, e3, integral_const_mul, integral_const_mul, E1, E2, E3, E4]
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, fourierTransform]
