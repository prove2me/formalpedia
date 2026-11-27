-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45OriginalPartIVFalseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:21:42.092773+00:00
-- url     : https://prove2.me/submissions/f51cf365-47c3-4b64-aa53-9a0259115493

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45OriginalPartIVDriftWitnessV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ZeroTimeObstruction
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The drift witness contradicts the proved zero-time obstruction. -/
theorem solution : ¬ Kyprianou.Ch04.certificate_ex4_5_ivV3 := by
  intro h
  letI m : MeasurableSpace ℕ := ⊥
  let P : Measure ℕ := Measure.dirac 0
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  obtain ⟨I,hI,hUCP⟩ := Kyprianou.Ch04.exercise45OriginalPartIVDriftWitnessV1 h
  exact Kyprianou.Ch04.exercise45ZeroTimeObstruction P rfl
    (fun w : ℕ => (w : ℝ)) (fun n => ⟨n,rfl⟩) I hI hUCP
