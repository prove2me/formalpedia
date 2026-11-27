-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45SurvivalEventStopMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:37:35.045458+00:00
-- url     : https://prove2.me/submissions/89bd6412-55b9-48d2-b868-ba892a90ec62

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (F : Filtration NNReal inferInstance)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal)))
    (s i : NNReal) (hi : s ≤ i) (A : Set Ω) (hA : MeasurableSet[F s] A)
    (hstop : IsStoppingTime F (fun w => (↑(min i (τ w)) : WithTop NNReal))) :
    MeasurableSet[hstop.measurableSpace] (A ∩ {w | s < τ w}) := by
  let B := A ∩ {w | s < τ w}
  have hB : MeasurableSet[F s] B := hA.inter (by
    simpa only [Set.compl_setOf, not_le, WithTop.coe_le_coe] using (ht s).compl)
  refine (hstop.measurableSet B).2 ⟨(le_iSup (fun t => F t) s) B hB,?_⟩
  intro u
  by_cases hu : s ≤ u
  · exact (F.mono hu B hB).inter (hstop u)
  · have he : B ∩ {w | (↑(min i (τ w)) : WithTop NNReal) ≤ ↑u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hu ((le_min hi (le_of_lt hw.1.2)).trans (WithTop.coe_le_coe.mp hw.2))
    rw [he]
    exact @MeasurableSet.empty Ω (F u)
