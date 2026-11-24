-- Prove2me | solution 2 for Kyprianou.Ch03.delayedClosedHitFixedApproxV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:50:04.342801+00:00
-- url     : https://prove2.me/submissions/db862837-eb08-4876-a604-774a43576bd4

import Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxUpperV1
import Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxLowerV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (B : Set ℝ) (hB : IsClosed B) (a : NNReal)
    (T : ℕ → Omega → WithTop NNReal)
    (hT : ∀ n w, T n w = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B}))
    (hStop : ∀ n, IsStoppingTime F (T n)) :
    ∀ᵐ w ∂P, (⨆ n, T n w) = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) := by
  have hu := Kyprianou.Ch03.delayedClosedHitFixedApproxUpperV1 P F X hX hNatural B hB a T hT hStop
  have hl := Kyprianou.Ch03.delayedClosedHitFixedApproxLowerV1 P F X hX hNatural B hB a T hT hStop
  filter_upwards [hl] with w hw
  exact le_antisymm (hu w) hw
