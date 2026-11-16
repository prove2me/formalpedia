-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum_indepIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:27:57.412208+00:00
-- url     : https://prove2.me/submissions/6a1a3662-53fc-48ba-a4c9-e9460dc6a583

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_independentLevySum_pairedIncrements

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Independent pairs of increments stay independent under coordinatewise addition. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    HasIndependentIncrements (fun t ω => X t ω + Y t ω) P := by
  intro n t ht
  have hp := Kyprianou.Ch01.independentLevySum_pairedIncrements
    P X Y hX hY hXY n t ht
  have hs := hp.comp (fun _ => fun p : ℝ × ℝ => p.1 + p.2)
    (by intro k; exact measurable_fst.add measurable_snd)
  change iIndepFun (fun k : Fin n => fun ω =>
    X (t k.succ) ω + Y (t k.succ) ω -
      (X (t k.castSucc) ω + Y (t k.castSucc) ω)) P
  simpa only [Function.comp_def, increment, sub_add_sub_comm] using hs
