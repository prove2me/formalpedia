-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_matching_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:37:14.86223+00:00
-- url     : https://prove2.me/submissions/a6dd3a9e-edca-49a0-9f16-4688228bb3d9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two increment families with matching distributions and almost sure limits have matching limiting laws. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : Filter NNReal) [l.NeBot] [l.IsCountablyGenerated]
    (U V : NNReal → Ω → ℝ) (D : Ω → ℝ)
    (hUm : ∀ s, AEMeasurable (U s) P) (hVm : ∀ s, AEMeasurable (V s) P)
    (hUL : ∀ᵐ w ∂P, Tendsto (fun s => U s w) l (nhds (D w)))
    (hVL : ∀ᵐ w ∂P, Tendsto (fun s => V s w) l (nhds (0 : ℝ)))
    (hLaw : ∀ s, P.map (U s) = P.map (V s)) :
    ∀ᵐ w ∂P, D w = 0 := by
  have hDm : AEMeasurable D P := aemeasurable_of_tendsto_metrizable_ae l hUm hUL
  have hUd := tendstoInDistribution_of_ae_tendsto hUm hDm hUL
  have hVd := tendstoInDistribution_of_ae_tendsto hVm measurable_const.aemeasurable hVL
  have hUd0 : TendstoInDistribution U l (fun _ : Ω => (0 : ℝ)) (fun _ => P) P := by
    refine ⟨hUm,measurable_const.aemeasurable,?_⟩
    simpa only [hLaw] using hVd.tendsto
  have hEq := tendstoInDistribution_unique U hUd hUd0
  have hZ := congrArg (fun μ : Measure ℝ => μ ({(0 : ℝ)}ᶜ)) hEq
  rw [Measure.map_apply_of_aemeasurable hDm (measurableSet_singleton _).compl] at hZ
  exact ae_iff.mpr (by simpa [Measure.map_const,Set.preimage] using hZ)
