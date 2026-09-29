-- Prove2me | solution 1 for InformationTheory.klDiv_le_klDiv_trim_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T15:49:56.609225+00:00
-- url     : https://prove2.me/submissions/d6955138-4196-47db-93bd-29222b212e60

import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# A σ-algebra that adds no information on a full-measure set does not change the divergence

If `m₁ ≤ m₂`, all the mass of `μ` and `ν` sits on `S`, and every `m₂`-set meets `S` in an
`m₁`-set (the two σ-algebras have the same trace on `S`), then
`klDiv_{m₂} μ ν ≤ klDiv_{m₁} (μ.trim) (ν.trim)`.

Together with the data-processing inequality this is an equality; only `≤` is recorded here,
since that is the direction that is not already available.

This is the half of L&S Exercise 14.13 (printed p. 197) that says the stopped σ-algebras
`F_{τ∧(n+1)}` and `F_{τ∧n}` carry the same information on the event `{τ ≤ n}`, where the
learner has already stopped and no further observation is made.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α : Type*}

theorem solution {m₁ m₂ : MeasurableSpace α} (h : m₁ ≤ m₂)
    (μ ν : @Measure α m₂) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set α} (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0)
    (htrace : ∀ A, MeasurableSet[m₂] A → MeasurableSet[m₁] (A ∩ S)) :
    @klDiv α m₂ μ ν ≤ @klDiv α m₁ (μ.trim h) (ν.trim h) := by
  classical
  by_cases hac : (μ.trim h) ≪ (ν.trim h)
  swap
  · rw [klDiv_of_not_ac hac]; exact le_top
  by_cases hint : Integrable (llr (μ.trim h) (ν.trim h)) (μ.trim h)
  swap
  · rw [klDiv_of_not_integrable hint]; exact le_top
  -- `S` itself is measurable, being `univ ∩ S`.
  have hS₁ : MeasurableSet[m₁] S := by simpa using htrace univ MeasurableSet.univ
  have hS₂ : MeasurableSet[m₂] S := h _ hS₁
  -- `g` is the `m₁`-density; we show it is also the `m₂`-density.
  set g : α → ℝ≥0∞ := (μ.trim h).rnDeriv (ν.trim h) with hg
  have hg_meas : Measurable[m₁] g := Measure.measurable_rnDeriv _ _
  have hg_meas₂ : Measurable[m₂] g := hg_meas.mono h le_rfl
  have hdiff : ∀ (ρ : @Measure α m₂) (A : Set α), ρ Sᶜ = 0 → ρ (A \ S) = 0 := fun ρ A hρ ↦
    measure_mono_null (fun x hx hxS ↦ hx.2 hxS) hρ
  have hμ_eq : ∀ A, MeasurableSet[m₂] A → μ A = μ (A ∩ S) := by
    intro A hA
    rw [← measure_inter_add_diff A hS₂, hdiff μ A hμS, add_zero]
  have hν_eq : ∀ A, MeasurableSet[m₂] A → ν A = ν (A ∩ S) := by
    intro A hA
    rw [← measure_inter_add_diff A hS₂, hdiff ν A hνS, add_zero]
  -- the key step: `g` is a density for `μ` with respect to `ν` on all of `m₂`
  have key : μ = ν.withDensity g := by
    ext A hA
    have hAS : MeasurableSet[m₁] (A ∩ S) := htrace A hA
    have hAS₂ : MeasurableSet[m₂] (A ∩ S) := h _ hAS
    have hsets : (A ∩ S : Set α) =ᵐ[ν] A := by
      rw [ae_eq_set]
      constructor
      · exact measure_mono_null (fun x hx ↦ absurd hx.1.1 hx.2) hνS
      · exact measure_mono_null (fun x hx hxS ↦ hx.2 ⟨hx.1, hxS⟩) hνS
    calc μ A = μ (A ∩ S) := hμ_eq A hA
      _ = (μ.trim h) (A ∩ S) := (trim_measurableSet_eq h hAS).symm
      _ = ∫⁻ x in A ∩ S, g x ∂(ν.trim h) := (Measure.setLIntegral_rnDeriv hac _).symm
      _ = ∫⁻ x, (A ∩ S).indicator g x ∂(ν.trim h) := by rw [lintegral_indicator hAS]
      _ = ∫⁻ x, (A ∩ S).indicator g x ∂ν := lintegral_trim h (hg_meas.indicator hAS)
      _ = ∫⁻ x in A ∩ S, g x ∂ν := by rw [lintegral_indicator hAS₂]
      _ = ∫⁻ x in A, g x ∂ν := setLIntegral_congr hsets
      _ = (ν.withDensity g) A := (withDensity_apply g hA).symm
  -- transfer absolute continuity, the log-likelihood ratio and integrability across the trim
  have hac₂ : μ ≪ ν := by rw [key]; exact withDensity_absolutelyContinuous ν g
  have hrn : μ.rnDeriv ν =ᵐ[ν] g := by
    rw [key]; exact Measure.rnDeriv_withDensity ν hg_meas₂
  have hllr : llr μ ν =ᵐ[μ] fun x ↦ Real.log (g x).toReal := by
    filter_upwards [hac₂ hrn] with x hx
    simp only [llr_def, hx]
  have hllr_trim : llr (μ.trim h) (ν.trim h) = fun x ↦ Real.log (g x).toReal := rfl
  have hint₂ : Integrable (llr μ ν) μ := by
    refine Integrable.congr ?_ hllr.symm
    have : Integrable (fun x ↦ Real.log (g x).toReal) (μ.trim h) := by
      rwa [hllr_trim] at hint
    exact integrable_of_integrable_trim h this
  -- both divergences are the same `ofReal`
  rw [klDiv_of_ac_of_integrable hac₂ hint₂, klDiv_of_ac_of_integrable hac hint]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  have hint_i : ∫ x, llr μ ν x ∂μ = ∫ x, llr (μ.trim h) (ν.trim h) x ∂(μ.trim h) := by
    rw [hllr_trim, integral_congr_ae hllr]
    exact integral_trim (μ := μ) h ((hg_meas.ennreal_toReal.log).stronglyMeasurable)
  have hμuniv : (μ.trim h).real univ = μ.real univ := by
    simp [measureReal_def, trim_measurableSet_eq h MeasurableSet.univ]
  have hνuniv : (ν.trim h).real univ = ν.real univ := by
    simp [measureReal_def, trim_measurableSet_eq h MeasurableSet.univ]
  rw [hint_i, hμuniv, hνuniv]
