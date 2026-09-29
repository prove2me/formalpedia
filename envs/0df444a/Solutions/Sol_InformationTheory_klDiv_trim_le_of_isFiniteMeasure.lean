-- Prove2me | solution 1 for InformationTheory.klDiv_trim_le_of_isFiniteMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:00:22.344103+00:00
-- url     : https://prove2.me/submissions/0ff0a9b8-f87d-4104-be12-aca651b2bc01

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Data-processing inequality for the Kullback-Leibler divergence, for finite measures

`klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν` for finite measures `μ`, `ν`.

This is L&S Exercise 14.10 (printed p. 196). The probability-measure case is already available;
the extension to finite measures is what one needs as soon as the space is split along an event,
since restricting a probability measure to a proper subset leaves a sub-probability measure.

The argument is the standard one: the density on the coarse σ-algebra is the conditional
expectation of the density on the fine one, and `klFun` is convex, so conditional Jensen applies.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem solution {α : Type*} {m m₀ : MeasurableSpace α}
    (hm : m ≤ m₀) (μ ν : @Measure α m₀)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    @klDiv α m (μ.trim hm) (ν.trim hm) ≤ @klDiv α m₀ μ ν := by
  letI : @IsFiniteMeasure α m (μ.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ univ⟩
  letI : @IsFiniteMeasure α m (ν.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top ν univ⟩
  by_cases htop : klDiv μ ν = ⊤
  · simp [htop]
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp htop).1
  have hint : Integrable (llr μ ν) μ := (klDiv_ne_top_iff.mp htop).2
  have hactrim : μ.trim hm ≪ ν.trim hm := hac.trim hm
  -- the fine density and its conditional expectation
  set f : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal with hf
  have hfint : Integrable f ν := Measure.integrable_toReal_rnDeriv
  have hphiint : Integrable (fun x ↦ klFun (f x)) ν :=
    (integrable_klFun_rnDeriv_iff hac).2 hint
  have hjensen : (fun x ↦ klFun (ν[f | m] x)) ≤ᵐ[ν] ν[fun x ↦ klFun (f x) | m] := by
    simpa [Function.comp_def] using
      (convexOn_klFun.map_condExp_le hm
        continuous_klFun.continuousOn.lowerSemicontinuousOn
        (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)
        isClosed_Ici hfint hphiint)
  have hcondphi : Integrable (ν[fun x ↦ klFun (f x) | m]) ν := integrable_condExp
  have hnonneg : 0 ≤ᵐ[ν] (fun x ↦ klFun (ν[f | m] x)) := by
    filter_upwards [condExp_nonneg (μ := ν) (f := f) (m := m)
      (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)] with x hx
    exact klFun_nonneg hx
  have hleftmeas : StronglyMeasurable[m] (fun x ↦ klFun (ν[f | m] x)) :=
    continuous_klFun.comp_stronglyMeasurable
      (stronglyMeasurable_condExp (μ := ν) (f := f) (m := m))
  have hleftint : Integrable (fun x ↦ klFun (ν[f | m] x)) ν :=
    Integrable.mono' hcondphi (hleftmeas.mono hm).aestronglyMeasurable
      (by
        filter_upwards [hjensen, hnonneg] with x hle hnn
        simpa [abs_of_nonneg hnn] using hle)
  have hrn := toReal_rnDeriv_trim hm hac
  -- the coarse divergence is finite too
  have htrimtop : @klDiv α m (μ.trim hm) (ν.trim hm) ≠ ⊤ := by
    refine klDiv_ne_top hactrim ?_
    rw [← integrable_klFun_rnDeriv_iff hactrim]
    refine (hleftint.trim hm hleftmeas).congr ?_
    filter_upwards [hrn] with x hx
    exact congrArg klFun hx.symm
  rw [← ENNReal.toReal_le_toReal htrimtop htop,
    toReal_klDiv_eq_integral_klFun hactrim, toReal_klDiv_eq_integral_klFun hac]
  calc ∫ x, klFun (((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) ∂ν.trim hm
      = ∫ x, klFun (ν[f | m] x) ∂ν.trim hm := by
        refine integral_congr_ae ?_
        filter_upwards [hrn] with x hx
        exact congrArg klFun hx
    _ = ∫ x, klFun (ν[f | m] x) ∂ν := (integral_trim (μ := ν) hm hleftmeas).symm
    _ ≤ ∫ x, ν[fun x ↦ klFun (f x) | m] x ∂ν := integral_mono_ae hleftint hcondphi hjensen
    _ = ∫ x, klFun (f x) ∂ν := integral_condExp hm
