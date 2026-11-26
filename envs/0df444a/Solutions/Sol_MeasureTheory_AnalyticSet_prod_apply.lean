-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.prod_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:18.36757+00:00
-- url     : https://prove2.me/submissions/6b978b24-794d-4bca-bbd9-bdd2003c58ac

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Theorems.Thm_MeasureTheory_AnalyticSet_nullMeasurableSet


set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {V W : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set (V × W)} (hS : AnalyticSet S)
    (μ : Measure V) [IsFiniteMeasure μ]
    (ν : Measure W) [IsFiniteMeasure ν] :
    μ.prod ν S = ∫⁻ v, ν (Prod.mk v ⁻¹' S) ∂μ := by
  obtain ⟨B, hBmeas, haeq⟩ := hS.nullMeasurableSet (μ.prod ν)
  have h1 : μ.prod ν S = μ.prod ν B := measure_congr haeq
  have hSB : μ.prod ν (S \ B) = 0 := ae_le_set.mp haeq.le
  have hBS : μ.prod ν (B \ S) = 0 := ae_le_set.mp haeq.symm.le
  -- measurable hulls of the two null differences
  set N₁ := toMeasurable (μ.prod ν) (S \ B) with hN₁
  set N₂ := toMeasurable (μ.prod ν) (B \ S) with hN₂
  have hN₁meas : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  have hN₂meas : MeasurableSet N₂ := measurableSet_toMeasurable _ _
  have hN₁null : μ.prod ν N₁ = 0 := by rw [hN₁, measure_toMeasurable]; exact hSB
  have hN₂null : μ.prod ν N₂ = 0 := by rw [hN₂, measure_toMeasurable]; exact hBS
  -- a.e. sections of the hulls are ν-null
  have hsec : ∀ (N : Set (V × W)), MeasurableSet N → μ.prod ν N = 0 →
      ∀ᵐ v ∂μ, ν (Prod.mk v ⁻¹' N) = 0 := by
    intro N hNmeas hNnull
    have hint := (Measure.prod_apply hNmeas).symm.trans hNnull
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_left hNmeas)).mp hint
  have hae : (fun v => ν (Prod.mk v ⁻¹' S)) =ᵐ[μ] fun v => ν (Prod.mk v ⁻¹' B) := by
    filter_upwards [hsec N₁ hN₁meas hN₁null, hsec N₂ hN₂meas hN₂null]
      with v hv1 hv2
    have hsub1 : Prod.mk v ⁻¹' S ⊆ (Prod.mk v ⁻¹' B) ∪ (Prod.mk v ⁻¹' N₁) := by
      intro w hw
      by_cases hwB : w ∈ Prod.mk v ⁻¹' B
      · exact Or.inl hwB
      · exact Or.inr (subset_toMeasurable _ _ ⟨hw, hwB⟩)
    have hsub2 : Prod.mk v ⁻¹' B ⊆ (Prod.mk v ⁻¹' S) ∪ (Prod.mk v ⁻¹' N₂) := by
      intro w hw
      by_cases hwS : w ∈ Prod.mk v ⁻¹' S
      · exact Or.inl hwS
      · exact Or.inr (subset_toMeasurable _ _ ⟨hw, hwS⟩)
    refine le_antisymm ?_ ?_
    · calc ν (Prod.mk v ⁻¹' S)
          ≤ ν ((Prod.mk v ⁻¹' B) ∪ (Prod.mk v ⁻¹' N₁)) := measure_mono hsub1
        _ ≤ ν (Prod.mk v ⁻¹' B) + ν (Prod.mk v ⁻¹' N₁) := measure_union_le _ _
        _ = ν (Prod.mk v ⁻¹' B) := by rw [hv1, add_zero]
    · calc ν (Prod.mk v ⁻¹' B)
          ≤ ν ((Prod.mk v ⁻¹' S) ∪ (Prod.mk v ⁻¹' N₂)) := measure_mono hsub2
        _ ≤ ν (Prod.mk v ⁻¹' S) + ν (Prod.mk v ⁻¹' N₂) := measure_union_le _ _
        _ = ν (Prod.mk v ⁻¹' S) := by rw [hv2, add_zero]
  rw [h1, Measure.prod_apply hBmeas, lintegral_congr_ae hae.symm]
end MeasureTheory.AnalyticSet
