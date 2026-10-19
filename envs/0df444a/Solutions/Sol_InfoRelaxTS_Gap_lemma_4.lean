-- Prove2me | solution 1 for InfoRelaxTS.Gap.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:22:13.941147+00:00
-- url     : https://prove2.me/submissions/bb42a17e-0067-4d6d-9b2b-9ed7d10d9c2d

import Mathlib
set_option autoImplicit false
open MeasureTheory

lemma aux_gauss_tail (σ z : ℝ) (hσ : 0 < σ) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi (0:ℝ), Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)) ≤ σ / z * Real.exp (-z ^ 2 / 2) := by
  set G : ℝ → ℝ := fun t => -(σ / z) * Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)) with hG
  set g : ℝ → ℝ := fun t => (z * σ + t) / (z * σ) * Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)) with hg
  have hder : ∀ t ∈ Set.Ici (0:ℝ), HasDerivAt G (g t) t := by
    intro t _
    have hp : HasDerivAt (fun t : ℝ => (z * σ + t) ^ 2) (2 * (z * σ + t)) t := by
      have h := (hasDerivAt_id t).const_add (z * σ)
      have := (hasDerivAt_pow 2 (z * σ + t)).comp t h
      refine this.congr_deriv ?_
      simp
    have h1 : HasDerivAt (fun t : ℝ => -(z * σ + t) ^ 2 / (2 * σ ^ 2))
        (-(2 * (z * σ + t)) / (2 * σ ^ 2)) t := (hp.neg).div_const (2 * σ ^ 2)
    have h2 := (h1.exp).const_mul (-(σ / z))
    refine h2.congr_deriv ?_
    simp only [hg]
    field_simp
  have hgnn : ∀ t ∈ Set.Ioi (0:ℝ), 0 ≤ g t := by
    intro t ht
    have : 0 < t := ht
    simp only [hg]
    positivity
  have hlim : Filter.Tendsto G Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => z * σ + t) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id
    have h1 : Filter.Tendsto (fun t : ℝ => (z * σ + t) ^ 2 / (2 * σ ^ 2)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_div_const (by positivity) ((Filter.tendsto_pow_atTop (by norm_num)).comp h0)
    have h2 : Filter.Tendsto (fun t : ℝ => -((z * σ + t) ^ 2 / (2 * σ ^ 2))) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h1
    have h3 := Real.tendsto_exp_atBot.comp h2
    have h4 := h3.const_mul (-(σ / z))
    simpa [hG, neg_div, Function.comp_def] using h4
  have hint : IntegrableOn g (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hder hgnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hder hint hlim
  have hdom : ∀ t ∈ Set.Ioi (0:ℝ), Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)) ≤ g t := by
    intro t ht
    have ht' : 0 < t := ht
    simp only [hg]
    have hc : 1 ≤ (z * σ + t) / (z * σ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [Real.exp_pos (-(z * σ + t) ^ 2 / (2 * σ ^ 2))]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)))
      (volume.restrict (Set.Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2))) (Set.Ioi 0) := by
    refine Integrable.mono' hint hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hdom t ht
  refine ⟨hI, ?_⟩
  calc ∫ t in Set.Ioi (0:ℝ), Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2))
      ≤ ∫ t in Set.Ioi (0:ℝ), g t := setIntegral_mono_on hI hint measurableSet_Ioi hdom
    _ = σ / z * Real.exp (-z ^ 2 / 2) := by
      rw [hval]
      simp only [hG]
      have : -(z * σ + 0) ^ 2 / (2 * σ ^ 2) = -z ^ 2 / 2 := by
        field_simp
        ring
      rw [this]; ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (σ : ℝ) (hσ : 0 < σ)
    (htail : ∀ z : ℝ, 0 ≤ z →
      (μ {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω}).toReal ≤ Real.exp (-z ^ 2 / 2)) :
    ∀ z : ℝ, 0 < z →
      ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ ≤ σ / z * Real.exp (-z ^ 2 / 2) := by
  intro z hz
  obtain ⟨hI, hv⟩ := aux_gauss_tail σ z hσ hz
  set m := ∫ x, X x ∂μ with hm
  have hfint : Integrable (fun ω => max (X ω - (m + z * σ)) 0) μ :=
    (hX.sub (integrable_const (m + z * σ))).pos_part
  have hfnn : 0 ≤ᵐ[μ] (fun ω => max (X ω - (m + z * σ)) 0) :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  rw [hfint.integral_eq_integral_meas_lt hfnn]
  refine le_trans ?_ hv
  refine integral_mono_of_nonneg ?_ hI ?_
  · exact Filter.Eventually.of_forall (fun t => ENNReal.toReal_nonneg)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun t ht => ?_))
    have ht' : 0 < t := ht
    have hsub : {a | t < max (X a - (m + z * σ)) 0} ⊆ {ω | m + (z + t / σ) * σ ≤ X ω} := by
      intro a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      have h1 : t < X a - (m + z * σ) := by
        rcases lt_max_iff.1 ha with h | h
        · exact h
        · linarith
      have : (z + t / σ) * σ = z * σ + t := by field_simp
      rw [this]; linarith
    calc μ.real {a | t < max (X a - (m + z * σ)) 0}
        ≤ μ.real {ω | m + (z + t / σ) * σ ≤ X ω} := measureReal_mono hsub
      _ ≤ Real.exp (-(z + t / σ) ^ 2 / 2) := htail _ (by positivity)
      _ = Real.exp (-(z * σ + t) ^ 2 / (2 * σ ^ 2)) := by
        congr 1; field_simp
