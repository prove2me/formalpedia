-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationCadlagCompositionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:34:05.485103+00:00
-- url     : https://prove2.me/submissions/5f289ec5-34c7-4fd0-a38b-32dcdb0a2234

import Theorems.Thm_Kyprianou_Ch02_cadlagCompMonotoneClockV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω)) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => X (τ t ω) ω) := by
  filter_upwards [hX.cadlag_ae, hτ.cadlag_ae, hmon] with ω hx hg hm
  exact Kyprianou.Ch02.cadlagCompMonotoneClockV1
    (fun t => X t ω) (fun t => τ t ω) hx hg hm
