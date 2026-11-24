-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_record_discount_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:49:43.964558+00:00
-- url     : https://prove2.me/submissions/2d5f42c6-0e7b-43de-96c5-45f3a52b3748

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q l : ℝ), 0 ≤ q → Integrable (fun ω => discountedAt q (tauPlus D.X l ω)) P := by
  intro Ω mΩ P hP D ψ W hψ hW q l hq
  obtain ⟨hm,hb,_⟩ := source_result81_measurable_ruin_path_reward q l hq
  have hu := (source_result81_strict_exit_clocks_aemeasurable Ω P D 0 l).1
  have hraw : AEMeasurable (fun ω => (tauPlus D.X l ω : ℝ≥0∞)) P := by
    have hs : shifted D.X 0 = D.X := by
      funext t ω
      simp [shifted]
    rw [hs] at hu
    exact hu
  refine (integrable_const (1:ℝ)).mono' (hm.comp_aemeasurable hraw).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have hh := hb (tauPlus D.X l ω : ℝ≥0∞)
    change |discountedAt q (tauPlus D.X l ω)| ≤ 1
    exact (abs_of_nonneg hh.1).le.trans hh.2)
