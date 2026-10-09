-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.measurable_prefix_vector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:11:26.588864+00:00
-- url     : https://prove2.me/submissions/ca1b1266-ee70-481f-9f81-3e76399467c9

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    Measurable (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) := by
  rw [measurable_pi_iff]
  intro i
  exact hM.meas i.1
