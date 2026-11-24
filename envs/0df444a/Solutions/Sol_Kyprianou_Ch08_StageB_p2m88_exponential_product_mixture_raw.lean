-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exponential_product_mixture_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:33:18.973461+00:00
-- url     : https://prove2.me/submissions/8add1dc4-1b51-4004-a152-c1f5b9174226

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_mixture_section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact exponential-measure translation. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ : ℝ), 0 < φ →
      ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A →
      let g : ℝ → ℝ≥0∞ := fun y =>
        ∫⁻ d in Ioc (x - y) x, ENNReal.ofReal (φ * Real.exp (-φ * (y - x + d))) ∂ν
      Measurable g ∧
        ((expMeasure φ).prod ν) {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} =
          ∫⁻ y in A, g y := by
  intro ν hν φ hφ x A hA
  classical
  dsimp only
  let E : Set (ℝ × ℝ) := {z | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A}
  let G : ℝ × ℝ → ℝ≥0∞ := fun z =>
    if x - z.1 < z.2 ∧ z.2 ≤ x then
      ENNReal.ofReal (φ * Real.exp (-φ * (z.1 - x + z.2))) else 0
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_snd measurable_const).inter
      (((measurable_const.add measurable_fst).sub measurable_snd) hA)
  have hG : Measurable G := by
    apply Measurable.ite
    · exact (measurableSet_lt (measurable_const.sub measurable_fst)
        measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
    · fun_prop
    · exact measurable_const
  have hinner (y : ℝ) : (∫⁻ d, G (y,d) ∂ν) =
      ∫⁻ d in Ioc (x - y) x, ENNReal.ofReal (φ * Real.exp (-φ * (y - x + d))) ∂ν := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro d
    simp only [G, Set.indicator, mem_Ioc]
  have hm : Measurable (fun y : ℝ => ∫⁻ d, G (y,d) ∂ν) :=
    Measurable.lintegral_prod_right (f := fun y d => G (y,d)) hG
  refine ⟨by simpa only [hinner] using hm, ?_⟩
  letI : IsProbabilityMeasure (expMeasure φ) := isProbabilityMeasure_expMeasure hφ
  change ((expMeasure φ).prod ν) E = _
  rw [Measure.prod_apply_symm hE]
  have hsection (d : ℝ) :
      expMeasure φ ((fun s : ℝ => (s,d)) ⁻¹' E) =
        ∫⁻ y in A, G (y,d) :=
    p2m88_exponential_mixture_section φ x d hφ A hA
  simp_rw [hsection]
  rw [← lintegral_lintegral_swap (μ := volume.restrict A) (ν := ν)
    (f := fun y d => G (y,d)) hG.aemeasurable]
  simp_rw [hinner]
