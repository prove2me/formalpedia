-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_barrier_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:04:33.922256+00:00
-- url     : https://prove2.me/submissions/31188ccb-4529-4dbd-98c7-adc9c72a386a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_occupation_sections_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ n : ℕ, Measurable (fun t : ℝ≥0 => P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A}) := by
  intro n
  let B : Set ℝ := (fun y : ℝ => y - ((n : ℝ) - x)) ⁻¹' A
  have hB : MeasurableSet B := (measurable_id.sub measurable_const) hA
  have hm := p2m88_source_occupation_sections_measurable Ω P D ψ hψ n
    (Nat.cast_nonneg n) B hB
  convert hm using 1
  funext t
  congr 1
  ext ω
  simp only [B, mem_preimage, mem_setOf_eq, shifted]
  have he : (n : ℝ) + D.X t ω - ((n : ℝ) - x) = x + D.X t ω := by ring
  rw [he]
