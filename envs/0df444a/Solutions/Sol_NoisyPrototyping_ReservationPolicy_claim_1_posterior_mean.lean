-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.claim_1_posterior_mean
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:01:37.168556+00:00
-- url     : https://prove2.me/submissions/3166e435-46fb-460d-bfde-fcbc4e000f80

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

open MeasureTheory
open NoisyPrototyping.ReservationPolicy

theorem solution (f : ℝ × ℝ → ℝ) (hf_nonneg : ∀ z, 0 ≤ f z)
    (hf_meas : Measurable f) (μ : Measure (ℝ × ℝ))
    (hμ : μ = (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f z)))
    [IsProbabilityMeasure μ] (hint : Integrable (fun z : ℝ × ℝ => z.1) μ) :
    (fun z : ℝ × ℝ => Q f z.2) =ᵐ[μ]
      μ[fun z : ℝ × ℝ => z.1 | MeasurableSpace.comap Prod.snd inferInstance] := by
  set F : ℝ × ℝ → NNReal := fun z => (f z).toNNReal with hFdef
  have hFm : Measurable F := hf_meas.real_toNNReal
  have hFf : ∀ z, (F z : ℝ) = f z := fun z => Real.coe_toNNReal _ (hf_nonneg z)
  have hμ' : μ = (volume : Measure (ℝ × ℝ)).withDensity (fun z => (F z : ENNReal)) := hμ
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume :=
    Measure.volume_eq_prod ℝ ℝ
  -- integrability transfer
  have hint_iff : ∀ g : ℝ × ℝ → ℝ, Integrable g μ ↔
      Integrable (fun z => f z * g z) ((volume : Measure ℝ).prod volume) := by
    intro g
    rw [hμ', integrable_withDensity_iff_integrable_smul hFm, ← hvol]
    simp only [NNReal.smul_def, smul_eq_mul, hFf]
  have hint_eq : ∀ g : ℝ × ℝ → ℝ, ∫ z, g z ∂μ =
      ∫ z, f z * g z ∂((volume : Measure ℝ).prod volume) := by
    intro g
    rw [hμ', integral_withDensity_eq_integral_smul hFm, ← hvol]
    simp only [NNReal.smul_def, smul_eq_mul, hFf]
  have hP : Integrable (fun z : ℝ × ℝ => f z * z.1) ((volume : Measure ℝ).prod volume) :=
    (hint_iff _).1 hint
  have h1 : Integrable (fun z : ℝ × ℝ => f z * 1) ((volume : Measure ℝ).prod volume) :=
    (hint_iff _).1 (integrable_const 1)
  simp only [mul_one] at h1
  -- a.e. slices
  have hslice1 := h1.prod_left_ae
  have hslice2 := hP.prod_left_ae
  set h : ℝ → ℝ := fun m => ∫ P : ℝ, f (P, m) with hh
  set k : ℝ → ℝ := fun m => ∫ P : ℝ, P * f (P, m) with hk
  have hQ : ∀ m, Q f m = k m / h m := fun m => rfl
  have hhm : Measurable h :=
    (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
      hf_meas.stronglyMeasurable).measurable
  have hkm : Measurable k :=
    (StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
      ((measurable_fst.mul hf_meas).stronglyMeasurable)).measurable
  have hQm : Measurable (Q f) := by
    have : Q f = fun m => k m / h m := rfl
    rw [this]; exact hkm.div hhm
  -- key a.e. identity
  have hkey : ∀ᵐ m ∂(volume : Measure ℝ), h m * Q f m = k m := by
    filter_upwards [hslice1, hslice2] with m hm1 hm2
    rw [hQ]
    by_cases h0 : h m = 0
    · have hz : (fun P => f (P, m)) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun P => hf_nonneg _) hm1).1 h0
      have : k m = 0 := by
        simp only [hk]
        rw [integral_eq_zero_of_ae]
        filter_upwards [hz] with P hP
        simp [hP]
      rw [h0, this]; simp
    · field_simp
  -- integrability of Q ∘ snd
  have hQint : Integrable (fun z : ℝ × ℝ => Q f z.2) μ := by
    rw [hint_iff]
    have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => f z * Q f z.2)
        ((volume : Measure ℝ).prod volume) :=
      (hf_meas.mul (hQm.comp measurable_snd)).aestronglyMeasurable
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [hslice1] with m hm1
      exact hm1.mul_const _
    · have hbound := (integrable_prod_iff' hP.aestronglyMeasurable).1 hP |>.2
      refine hbound.mono' ?_ ?_
      · exact ((StronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
          ((hf_meas.mul (hQm.comp measurable_snd)).norm.stronglyMeasurable))).aestronglyMeasurable
      · filter_upwards [hkey] with m hm
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        have e1 : (∫ P : ℝ, ‖f (P, m) * Q f m‖) = |k m| := by
          have : (fun P : ℝ => ‖f (P, m) * Q f m‖) = fun P => f (P, m) * |Q f m| := by
            funext P; rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
          rw [this, integral_mul_const, ← hm, abs_mul, abs_of_nonneg
            (integral_nonneg (fun P => hf_nonneg _))]
        rw [e1]
        calc |k m| = ‖∫ P : ℝ, f (P, m) * P‖ := by
              rw [Real.norm_eq_abs]; congr 1; simp only [hk]; congr 1; funext P; ring
          _ ≤ ∫ P : ℝ, ‖f (P, m) * P‖ := norm_integral_le_integral_norm _
  -- set integral formula
  have hset : ∀ (g : ℝ × ℝ → ℝ), Integrable g μ → ∀ B : Set ℝ, MeasurableSet B →
      ∫ z in Prod.snd ⁻¹' B, g z ∂μ =
        ∫ m, B.indicator (fun m => ∫ P : ℝ, f (P, m) * g (P, m)) m := by
    intro g hg B hB
    have hs : MeasurableSet (Prod.snd ⁻¹' B : Set (ℝ × ℝ)) := measurable_snd hB
    rw [← integral_indicator hs, hint_eq]
    have hgi : Integrable (fun z => f z * (Prod.snd ⁻¹' B).indicator g z)
        ((volume : Measure ℝ).prod volume) := (hint_iff _).1 (hg.indicator hs)
    rw [integral_prod_symm _ hgi]
    congr 1; funext m
    by_cases hm : m ∈ B
    · rw [Set.indicator_of_mem hm]
      congr 1; funext P
      rw [Set.indicator_of_mem (show (P, m) ∈ Prod.snd ⁻¹' B from hm)]
    · rw [Set.indicator_of_notMem hm]
      have : (fun P : ℝ => f (P, m) * (Prod.snd ⁻¹' B).indicator g (P, m)) = fun _ => 0 := by
        funext P
        rw [Set.indicator_of_notMem (show (P, m) ∉ Prod.snd ⁻¹' B from hm), mul_zero]
      rw [this, integral_zero]
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_snd.comap_le hint
    (fun s _ _ => hQint.integrableOn) ?_ ?_
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := hs
    rw [hset _ hQint B hB, hset _ hint B hB]
    apply integral_congr_ae
    filter_upwards [hkey] with m hm
    by_cases hmB : m ∈ B
    · rw [Set.indicator_of_mem hmB, Set.indicator_of_mem hmB]
      rw [integral_mul_const, hm, hk]
      show ∫ (P : ℝ), P * f (P, m) = ∫ (P : ℝ), f (P, m) * P
      congr 1; funext P; ring
    · rw [Set.indicator_of_notMem hmB, Set.indicator_of_notMem hmB]
  · exact (hQm.comp (comap_measurable Prod.snd)).aestronglyMeasurable
