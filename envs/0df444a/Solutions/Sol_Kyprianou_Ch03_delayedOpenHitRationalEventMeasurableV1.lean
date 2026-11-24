-- Prove2me | solution 1 for Kyprianou.Ch03.delayedOpenHitRationalEventMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:31:06.917893+00:00
-- url     : https://prove2.me/submissions/388a81b0-b562-4c76-bd73-b974d252a46f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (a s : NNReal) (B : Set ℝ) (hB : IsOpen B) :
    MeasurableSet[F s] (⋃ q : ℚ, ⋃ (_ : a ≤ Real.toNNReal q ∧ Real.toNNReal q < s),
      {w | X (Real.toNNReal q) w ∈ B}) := by
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  apply F.mono hq.2.le
  rw [hNatural (Real.toNNReal q)]
  refine (le_sup_left : PerfCorrMSQ.natFiltr X (Real.toNNReal q) ≤ _) _ ?_
  refine (le_iSup₂ (f := fun v (_ : v ≤ Real.toNNReal q) =>
    MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace ℝ))
      (Real.toNNReal q) le_rfl) _ ?_
  exact ⟨B, hB.measurableSet, rfl⟩
