-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_psi_differentiable_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:34:01.127318+00:00
-- url     : https://prove2.me/submissions/b56859ee-1661-4c84-8adc-f2343d23eae6

import Mathlib.Probability.Moments.MGFAnalytic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful analytic reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ β : ℝ, 0 < β → DifferentiableAt ℝ ψ β := by
  intro Ω mΩ P hP D ψ hψ β hβ
  have hsub : Ioi (0 : ℝ) ⊆ integrableExpSet (D.X 1) P := by
    intro x hx
    change Integrable (fun ω => Real.exp (x * D.X 1 ω)) P
    exact (hψ x 1 (le_of_lt hx) (by norm_num)).1
  have hi : β ∈ interior (integrableExpSet (D.X 1) P) := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Ioi_mem_nhds hβ) hsub
  have hc := (ProbabilityTheory.analyticAt_cgf hi).differentiableAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hβ] with x hx
  have h := (hψ x 1 (le_of_lt hx) (by norm_num)).2
  simpa [SpectrallyNegativeModel.toData, ProbabilityTheory.cgf,
    ProbabilityTheory.mgf] using h
