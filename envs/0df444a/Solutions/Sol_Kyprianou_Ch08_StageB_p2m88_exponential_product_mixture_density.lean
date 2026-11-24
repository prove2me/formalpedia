-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exponential_product_mixture_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:14:56.984127+00:00
-- url     : https://prove2.me/submissions/6b3251b0-a3dd-4ecf-9171-d815b7e12308

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_product_mixture_raw
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact exponential-measure translation. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ), 0 < φ → 0 < q →
      ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A →
      (ENNReal.ofReal q)⁻¹ * ((expMeasure φ).prod ν)
        {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} =
      ∫⁻ y in A, (ENNReal.ofReal (φ / q * Real.exp (-φ * (y - x)))) *
        (∫⁻ z in Ioc (x - y) x, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν)
        ∂(volume.restrict (Ici (0 : ℝ))) := by
  intro ν hν φ q hφ hq x A hA
  let f : ℝ → ℝ≥0∞ := fun y =>
    ∫⁻ d in Ioc (x - y) x, ENNReal.ofReal (φ * Real.exp (-φ * (y-x+d))) ∂ν
  let g : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (φ/q * Real.exp (-φ * (y-x))) *
      ∫⁻ d in Ioc (x-y) x, ENNReal.ofReal (Real.exp (-φ*d)) ∂ν
  obtain ⟨hf, hraw⟩ := p2m88_exponential_product_mixture_raw ν φ hφ x A hA
  change (ENNReal.ofReal q)⁻¹ * ((expMeasure φ).prod ν)
    {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} =
      ∫⁻ y in A, g y ∂(volume.restrict (Ici (0 : ℝ)))
  rw [hraw]
  have hfm : Measurable f := hf
  change (ENNReal.ofReal q)⁻¹ * (∫⁻ y in A, f y) = _
  rw [← lintegral_const_mul _ hfm]
  have hpoint : (fun y => (ENNReal.ofReal q)⁻¹ * f y) =
      (Ici (0 : ℝ)).indicator g := by
    funext y
    by_cases hy : 0 ≤ y
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
      have hfact : f y = ENNReal.ofReal (φ * Real.exp (-φ * (y-x))) *
          ∫⁻ d in Ioc (x-y) x, ENNReal.ofReal (Real.exp (-φ*d)) ∂ν := by
        dsimp [f]
        rw [← lintegral_const_mul _ (by fun_prop)]
        apply lintegral_congr
        intro d
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -φ*(y-x+d) = -φ*(y-x) + -φ*d by ring, Real.exp_add]
        ring
      rw [hfact, ← mul_assoc]
      dsimp [g]
      congr 1
      rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_div_of_pos hq]
      congr 1
      ring
    · have hset : Ioc (x-y) x = ∅ := by
        ext d
        constructor
        · intro hd
          exact False.elim (by have h1 := hd.1; have h2 := hd.2; linarith)
        · intro hd
          exact False.elim hd
      simp [f, hset, hy]
  rw [hpoint, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, Measure.restrict_restrict hA, inter_comm]
