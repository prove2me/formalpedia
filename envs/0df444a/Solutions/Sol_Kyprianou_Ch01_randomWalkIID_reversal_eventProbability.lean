-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkIID_reversal_eventProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:23:25.022276+00:00
-- url     : https://prove2.me/submissions/23f07cc3-850b-4fd1-917e-1b516c9c5452

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_randomWalkIID_reversal_jointLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

/-- Transport a measurable finite-vector event across an iid reversal. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ i : ℕ, Measurable (increment i))
    (hindep : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hLaw : ∀ i : ℕ, HasLaw (increment i) jumpLaw P)
    (n : ℕ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    P {ω | (fun i : Fin n => increment i ω) ∈ E} =
      P {ω | (fun i : Fin n => increment (Fin.rev i) ω) ∈ E} := by
  have hforward : Measurable
      (fun ω => fun i : Fin n => increment i ω) :=
    measurable_pi_iff.mpr (fun i => hmeas i)
  have hreverse : Measurable
      (fun ω => fun i : Fin n => increment (Fin.rev i) ω) :=
    measurable_pi_iff.mpr (fun i => hmeas (Fin.rev i))
  have heq :=
    Kyprianou.Ch01.randomWalkIID_reversal_jointLaw
      P increment hindep jumpLaw hLaw n
  calc
    P {ω | (fun i : Fin n => increment i ω) ∈ E} =
        (P.map (fun ω => fun i : Fin n => increment i ω)) E := by
          exact (Measure.map_apply hforward hE).symm
    _ = (P.map (fun ω => fun i : Fin n => increment (Fin.rev i) ω)) E := by
          rw [heq]
    _ = P {ω | (fun i : Fin n => increment (Fin.rev i) ω) ∈ E} := by
          exact Measure.map_apply hreverse hE
