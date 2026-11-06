-- Prove2me | solution 1 for LinParamBandits.UEFinite.gap_min_expectation_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:23:20.520505+00:00
-- url     : https://prove2.me/submissions/2d995f53-25aa-46d0-91a8-d38828312179

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

open MeasureTheory ProbabilityTheory

namespace UEFinGapMinAux

open LinParamBandits.UEFinite

variable {r : ℕ}

lemma bestValue_eq_sup' (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (h𝒰ne : 𝒰.Nonempty) (z : LinParamBandits.LowerBound.Vec r) :
    LinParamBandits.UEGeneral.bestValue 𝒰 z =
      h𝒰fin.toFinset.sup' (by simpa using h𝒰ne) (fun v => inner ℝ v z) := by
  rw [Finset.sup'_eq_csSup_image, Set.Finite.coe_toFinset]
  rfl

lemma continuous_gap (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (h𝒰ne : 𝒰.Nonempty) (u : LinParamBandits.LowerBound.Vec r) :
    Continuous (fun z => gap 𝒰 u z) := by
  have : (fun z => gap 𝒰 u z) = fun z =>
      h𝒰fin.toFinset.sup' (by simpa using h𝒰ne) (fun v => inner ℝ v z) - inner ℝ u z := by
    funext z; unfold gap; rw [bestValue_eq_sup' 𝒰 h𝒰fin h𝒰ne]
  rw [this]
  refine Continuous.sub ?_ (by fun_prop)
  exact Continuous.finset_sup'_apply _ (fun v _ => by fun_prop)

lemma gap_nonneg (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    0 ≤ gap 𝒰 u z := by
  unfold gap LinParamBandits.UEGeneral.bestValue
  have : inner ℝ u z ≤ sSup ((fun v => inner ℝ v z) '' 𝒰) :=
    le_csSup (h𝒰fin.image _).bddAbove ⟨u, hu, rfl⟩
  linarith

end UEFinGapMinAux

open UEFinGapMinAux in
theorem solution
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (μ : Measure (LinParamBandits.LowerBound.Vec r)) (hμ : IsProbabilityMeasure μ)
    (M₀ : ℝ) (hM₀ : 0 < M₀) (hdens : LinParamBandits.UEFinite.GapDensityLe 𝒰 μ M₀ u) (T : ℕ) (hT : r + 1 ≤ T) :
    Integrable (fun z => min (Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z)) μ ∧
    ∫ z, min (Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z) (T * LinParamBandits.UEFinite.gap 𝒰 u z) ∂μ ≤
      (M₀ + 1) * Real.log T + M₀ * Real.log T ^ 2 := by
  set L := Real.log T with hL
  set Δ := fun z => LinParamBandits.UEFinite.gap 𝒰 u z with hΔ
  have hTpos : (3 : ℝ) ≤ T := by exact_mod_cast (show 3 ≤ T by omega)
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  set g : ℝ → ℝ := fun x => min (L / x) (T * x) with hg
  have hgm : Measurable g := by
    simp only [hg]; exact (measurable_const.div measurable_id).min (measurable_const.mul measurable_id)
  have hΔc : Continuous Δ := continuous_gap 𝒰 h𝒰fin h𝒰ne u
  have hΔm : Measurable Δ := hΔc.measurable
  have hΔnn : ∀ z, 0 ≤ Δ z := fun z => gap_nonneg 𝒰 h𝒰fin u hu z
  have hgnn : ∀ x, 0 ≤ x → 0 ≤ g x := by
    intro x hx
    simp only [hg]
    exact le_min (div_nonneg hL0 hx) (mul_nonneg (by positivity) hx)
  -- the lintegral bound
  set F : ℝ → ENNReal := fun x => ENNReal.ofReal (g x) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hgm
  set ν := μ.map Δ with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hΔm.aemeasurable
  have hmap : ∫⁻ z, ENNReal.ofReal (g (Δ z)) ∂μ = ∫⁻ x, F x ∂ν := by
    rw [hν, lintegral_map hFm hΔm]
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hsplit := lintegral_add_compl F (μ := ν) hS
  -- complement part
  have hcompl : ∫⁻ x in (Set.Ioc (0 : ℝ) 1)ᶜ, F x ∂ν ≤ ENNReal.ofReal L := by
    calc ∫⁻ x in (Set.Ioc (0 : ℝ) 1)ᶜ, F x ∂ν ≤ ∫⁻ x in (Set.Ioc (0 : ℝ) 1)ᶜ, ENNReal.ofReal L ∂ν := by
          apply setLIntegral_mono measurable_const
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and, not_le] at hx
          simp only [hF]
          apply ENNReal.ofReal_le_ofReal
          by_cases hx0 : 0 < x
          · have hx1 := hx hx0
            simp only [hg]
            refine (min_le_left _ _).trans ?_
            rw [div_le_iff₀ hx0]; nlinarith
          · push Not at hx0
            simp only [hg]
            refine (min_le_right _ _).trans ?_
            have : (T : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hx0
            linarith
      _ = ENNReal.ofReal L * ν (Set.Ioc (0 : ℝ) 1)ᶜ := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal L * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal L := mul_one _
  -- Ioc 0 1 part
  have hrestr : ν.restrict (Set.Ioc (0 : ℝ) 1) ≤
      ENNReal.ofReal M₀ • volume.restrict (Set.Ioc (0 : ℝ) 1) := by
    have h1 : ν.restrict (Set.Ioc (0 : ℝ) 1) = (ν.restrict (Set.Ioi 0)).restrict (Set.Ioc (0 : ℝ) 1) := by
      rw [Measure.restrict_restrict hS, Set.Ioc_inter_Ioi]
      simp
    have h2 : (volume.restrict (Set.Ioi (0:ℝ))).restrict (Set.Ioc (0 : ℝ) 1) =
        volume.restrict (Set.Ioc (0 : ℝ) 1) := by
      rw [Measure.restrict_restrict hS, Set.Ioc_inter_Ioi]
      simp
    rw [h1, ← h2, ← Measure.restrict_smul]
    exact Measure.restrict_mono le_rfl hdens
  have hTinv : (1 : ℝ) / T ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hTinvpos : (0 : ℝ) < 1 / T := by positivity
  have hIoc : ∫⁻ x in Set.Ioc (0 : ℝ) 1, F x ≤ ENNReal.ofReal 1 + ENNReal.ofReal (L * L) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hTinvpos.le hTinv,
      lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
    gcongr
    · calc ∫⁻ x in Set.Ioc (0 : ℝ) (1 / T), F x ≤ ∫⁻ x in Set.Ioc (0 : ℝ) (1 / T), ENNReal.ofReal 1 := by
            apply setLIntegral_mono measurable_const
            intro x hx
            simp only [hF, hg]
            apply ENNReal.ofReal_le_ofReal
            refine (min_le_right _ _).trans ?_
            have := hx.2
            rw [le_div_iff₀ (by linarith)] at this
            linarith
        _ = ENNReal.ofReal 1 * ENNReal.ofReal (1 / T - 0) := by
            rw [setLIntegral_const, Real.volume_Ioc]
        _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal 1 := by
            gcongr; linarith
        _ = ENNReal.ofReal 1 := by simp
    · calc ∫⁻ x in Set.Ioc (1 / T : ℝ) 1, F x ≤ ∫⁻ x in Set.Ioc (1 / T : ℝ) 1, ENNReal.ofReal (L * x⁻¹) := by
            apply setLIntegral_mono
            · exact ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_inv)
            intro x hx
            simp only [hF, hg]
            apply ENNReal.ofReal_le_ofReal
            refine (min_le_left _ _).trans (le_of_eq ?_)
            rw [div_eq_mul_inv]
        _ = ENNReal.ofReal (∫ x in Set.Ioc (1 / T : ℝ) 1, L * x⁻¹) := by
            rw [ofReal_integral_eq_lintegral_ofReal]
            · have hcont : ContinuousOn (fun x : ℝ => L * x⁻¹) (Set.Icc (1 / T : ℝ) 1) := by
                apply ContinuousOn.mul continuousOn_const
                apply ContinuousOn.inv₀ continuousOn_id
                intro x hx; have := hx.1; simp only [id]; linarith
              exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
              have := hx.1
              exact mul_nonneg hL0 (inv_nonneg.mpr (by linarith))
        _ = ENNReal.ofReal (L * L) := by
            congr 1
            rw [← intervalIntegral.integral_of_le hTinv, intervalIntegral.integral_const_mul,
              integral_inv_of_pos hTinvpos one_pos]
            congr 1
            rw [hL]; congr 1; field_simp
  have hpart : ∫⁻ x in Set.Ioc (0 : ℝ) 1, F x ∂ν ≤ ENNReal.ofReal M₀ * (ENNReal.ofReal 1 + ENNReal.ofReal (L * L)) := by
    calc ∫⁻ x in Set.Ioc (0 : ℝ) 1, F x ∂ν ≤ ∫⁻ x, F x ∂(ENNReal.ofReal M₀ • volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
          lintegral_mono' hrestr le_rfl
      _ = ENNReal.ofReal M₀ * ∫⁻ x in Set.Ioc (0 : ℝ) 1, F x := by
          rw [lintegral_smul_measure]; rfl
      _ ≤ _ := by gcongr
  have hbound : ∫⁻ z, ENNReal.ofReal (g (Δ z)) ∂μ ≤
      ENNReal.ofReal ((M₀ + 1) * L + M₀ * L ^ 2) := by
    rw [hmap, ← hsplit]
    calc _ ≤ ENNReal.ofReal M₀ * (ENNReal.ofReal 1 + ENNReal.ofReal (L * L)) + ENNReal.ofReal L :=
          add_le_add hpart hcompl
      _ = ENNReal.ofReal (M₀ * (1 + L * L) + L) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul hM₀.le,
            ← ENNReal.ofReal_add (by positivity) hL0]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith
  have hfm : Measurable (fun z => g (Δ z)) := hgm.comp hΔm
  have hfnn : ∀ z, 0 ≤ g (Δ z) := fun z => hgnn _ (hΔnn z)
  have hint : Integrable (fun z => g (Δ z)) μ := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfnn)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  change ∫ z, g (Δ z) ∂μ ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfnn) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
