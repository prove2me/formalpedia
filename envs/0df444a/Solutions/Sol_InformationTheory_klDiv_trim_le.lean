-- Prove2me | solution 1 for InformationTheory.klDiv_trim_le
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T20:08:26.699701+00:00
-- url     : https://prove2.me/submissions/6f428d76-9e96-4106-afd0-93cb672d8336

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem solution {α : Type*} {m m₀ : MeasurableSpace α}
    (hm : m ≤ m₀) (μ ν : @Measure α m₀)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    @klDiv α m (μ.trim hm) (ν.trim hm) ≤ @klDiv α m₀ μ ν := by
  letI : @IsProbabilityMeasure α m (μ.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]⟩
  letI : @IsProbabilityMeasure α m (ν.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]⟩
  by_cases htop : klDiv μ ν = ⊤
  · simp [htop]
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp htop).1
  have hint : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp htop).2
  have hactrim : μ.trim hm ≪ ν.trim hm := hac.trim hm
  have htrimtop : @klDiv α m (μ.trim hm) (ν.trim hm) ≠ ⊤ := by
    refine klDiv_ne_top hactrim ?_
    rw [← integrable_klFun_rnDeriv_iff hactrim]
    let f : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
    have hfint : Integrable f ν := Measure.integrable_toReal_rnDeriv
    have hphiint : Integrable (fun x ↦ klFun (f x)) ν :=
      (integrable_klFun_rnDeriv_iff hac).2 hint
    have hjensen :
        (fun x ↦ klFun (ν[f | m] x)) ≤ᵐ[ν]
          ν[fun x ↦ klFun (f x) | m] := by
      simpa [Function.comp_def] using
        (convexOn_klFun.map_condExp_le hm
          continuous_klFun.continuousOn.lowerSemicontinuousOn
          (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)
          isClosed_Ici hfint hphiint)
    have hcondphi : Integrable (ν[fun x ↦ klFun (f x) | m]) ν :=
      integrable_condExp
    have hnonneg : 0 ≤ᵐ[ν] (fun x ↦ klFun (ν[f | m] x)) := by
      filter_upwards [condExp_nonneg (μ := ν)
        (f := f) (m := m) (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)] with x hx
      exact klFun_nonneg hx
    have hleftmeas : StronglyMeasurable[m] (fun x ↦ klFun (ν[f | m] x)) :=
      continuous_klFun.comp_stronglyMeasurable
        (stronglyMeasurable_condExp (μ := ν) (f := f) (m := m))
    have hleftint : Integrable (fun x ↦ klFun (ν[f | m] x)) ν :=
      Integrable.mono' hcondphi
        (hleftmeas.mono hm).aestronglyMeasurable
        (by
          filter_upwards [hjensen, hnonneg] with x hle hnonneg
          simpa [abs_of_nonneg hnonneg] using hle)
    have hrn := toReal_rnDeriv_trim hm hac
    refine (hleftint.trim hm hleftmeas).congr ?_
    filter_upwards [hrn] with x hx
    exact congrArg klFun hx.symm
  rw [← ENNReal.toReal_le_toReal htrimtop htop]
  rw [toReal_klDiv_eq_integral_klFun hactrim,
    toReal_klDiv_eq_integral_klFun hac]
  let f : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hfint : Integrable f ν := Measure.integrable_toReal_rnDeriv
  have hphiint : Integrable (fun x ↦ klFun (f x)) ν :=
    (integrable_klFun_rnDeriv_iff hac).2 hint
  have hjensen :
      (fun x ↦ klFun (ν[f | m] x)) ≤ᵐ[ν]
        ν[fun x ↦ klFun (f x) | m] := by
    simpa [Function.comp_def] using
      (convexOn_klFun.map_condExp_le hm
        continuous_klFun.continuousOn.lowerSemicontinuousOn
        (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)
        isClosed_Ici hfint hphiint)
  have hcondphi : Integrable (ν[fun x ↦ klFun (f x) | m]) ν :=
    integrable_condExp
  have hnonneg : 0 ≤ᵐ[ν] (fun x ↦ klFun (ν[f | m] x)) := by
    filter_upwards [condExp_nonneg (μ := ν)
      (f := f) (m := m) (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)] with x hx
    exact klFun_nonneg hx
  have hleftmeas : StronglyMeasurable[m] (fun x ↦ klFun (ν[f | m] x)) :=
    continuous_klFun.comp_stronglyMeasurable
      (stronglyMeasurable_condExp (μ := ν) (f := f) (m := m))
  have hleftint : Integrable (fun x ↦ klFun (ν[f | m] x)) ν :=
    Integrable.mono' hcondphi
      (hleftmeas.mono hm).aestronglyMeasurable
      (by
        filter_upwards [hjensen, hnonneg] with x hle hnonneg
        simpa [abs_of_nonneg hnonneg] using hle)
  have hrn := toReal_rnDeriv_trim hm hac
  calc
    ∫ x, klFun (((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) ∂ν.trim hm =
        ∫ x, klFun (ν[f | m] x) ∂ν.trim hm := by
      apply integral_congr_ae
      filter_upwards [hrn] with x hx
      exact congrArg klFun hx
    _ = ∫ x, klFun (ν[f | m] x) ∂ν := by
      rw [integral_trim hm hleftmeas]
    _ ≤ ∫ x, ν[fun x ↦ klFun (f x) | m] x ∂ν :=
      integral_mono_ae hleftint hcondphi hjensen
    _ = ∫ x, klFun (f x) ∂ν := integral_condExp hm
