-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_zero_discount_bounded_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:44:36.304802+00:00
-- url     : https://prove2.me/submissions/24a9a2c9-29d5-4fdc-804d-758cc75c7ff7

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_discount_sequence_properties
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_phi_discount_sequence_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_occupation_sections_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_killed_density_bounded_integral_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_discounted_time_integral_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qpos_set_identity
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W → ∀ x : ℝ, 0 ≤ x →
      ∀ B : ℝ, 0 ≤ B → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Iic B →
      ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A =
      ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW x hx B hB A hA hsub
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  obtain ⟨hr, ha, ht⟩ := p2m88_discount_sequence_properties
  have hφ := p2m88_source_phi_discount_sequence_limit Ω P D ψ hψ r
    (fun n => (hr n).1) ht
  have hd := p2m88_killed_density_bounded_integral_limit ψ W hW r hr ht hφ
    x hx B hB A hA hsub
  let f : ℝ≥0 → ℝ≥0∞ := fun t => P {ω | (t : WithTop ℝ≥0) <
    tauMinus (shifted D.X x) 0 ω ∧ shifted D.X x t ω ∈ A}
  have hf : Measurable f := p2m88_source_occupation_sections_measurable Ω P D ψ hψ x hx A hA
  have htime := p2m88_discounted_time_integral_limit positiveTimeLebesgue f hf r ha ht
  have htime' := htime.congr (fun n =>
    (p2m88_halfline_occupation_qpos_set_identity Ω P D ψ W hψ hW (r n) x (hr n).1 hx A hA).symm)
  exact tendsto_nhds_unique hd htime'
