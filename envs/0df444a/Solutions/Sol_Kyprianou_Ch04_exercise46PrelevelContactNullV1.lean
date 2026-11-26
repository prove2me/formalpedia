-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PrelevelContactNullV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:18:49.709843+00:00
-- url     : https://prove2.me/submissions/e427c844-6d17-49e7-a1fa-b048c5fbdc08

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46MappedClockNullSingletonV1
import Theorems.Thm_Kyprianou_Ch04_exercise46CountableSectionsProductNullV2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (T : NNReal) (E : Set (NNReal × Omega)) (hE : MeasurableSet E)
    (hCount : ∀ᵐ w ∂P, {t : NNReal | (t,w) ∈ E}.Countable) :
    ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E = 0 := by
  let mT : Measure NNReal :=
    ((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal
  letI : IsFiniteMeasure ((volume : Measure Real).restrict (Icc 0 (T : Real))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure mT := Measure.isFiniteMeasure_map _ _
  letI : NullSingletonClass mT := Kyprianou.Ch04.exercise46MappedClockNullSingletonV1 T
  have h := Kyprianou.Ch04.exercise46CountableSectionsProductNullV2 P mT
    (Prod.swap ⁻¹' E) (measurable_swap hE) hCount
  change (mT.prod P) E = 0
  rw [← Measure.prod_swap, Measure.map_apply measurable_swap hE]
  exact h
