-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:03:07.751182+00:00
-- url     : https://prove2.me/submissions/e90304ba-6d65-4d8a-8794-949f0c3299be

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup

open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F) :
    Adapted F X := by
  intro u B hB
  rw [hNatural u]
  apply (le_sup_left : PerfCorrMSQ.natFiltr X u ≤ _)
  exact (le_iSup₂ (f := fun v (_ : v ≤ u) =>
    MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace ℝ)) u le_rfl) _
      ⟨B, hB, rfl⟩
