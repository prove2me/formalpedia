-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49SpikeTimeV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:53:40.171925+00:00
-- url     : https://prove2.me/submissions/056df87f-2caf-49a9-824e-2dda2d4865ac

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (a : NNReal) (ha : 0 < a) :
    sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
      (if t = a then (-1 : ℝ) else 0) < 0} = (a : WithTop NNReal) := by
  have he : {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
      (if t = a then (-1 : ℝ) else 0) < 0} = {(a : WithTop NNReal)} := by
    ext v
    constructor
    · rintro ⟨t,rfl,_,ht⟩
      have h : t = a := by
        by_contra hn
        simp [hn] at ht
      change (t : WithTop NNReal) = (a : WithTop NNReal)
      rw [h]
    · intro hv
      have h : v = (a : WithTop NNReal) := hv
      exact ⟨a,h,ha,by simp⟩
  rw [he,sInf_singleton]
