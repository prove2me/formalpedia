-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.measurable_eval_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:55:01.305248+00:00
-- url     : https://prove2.me/submissions/2db36341-ca49-4364-bd0e-4098274cd7ec

import Mathlib.Probability.Process.Stopping
import Definitions.Def_MarkovProcess_ContinuousPath
open MeasureTheory MarkovProcess MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

theorem solution (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable[hT.measurableSpace] (fun omega ↦ omega (T omega)) := by
  have hprog : IsStronglyProgressive (canonicalFiltration (alpha := alpha))
      (coordinateProcess (alpha := alpha)) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (measurable_coordinateProcess_canonicalFiltration t).stronglyMeasurable)
      (fun ω => ω.continuous)
  have h := measurable_stoppedValue hprog hT
  have e : stoppedValue (coordinateProcess (alpha := alpha)) (fun omega ↦ (T omega : WithTop NNReal))
      = fun omega ↦ omega (T omega) := by
    funext omega; rfl
  rwa [e] at h
