-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.indep_prefix_next_demand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:18:33.065303+00:00
-- url     : https://prove2.me/submissions/d226fd13-a447-41ad-9f97-41a5a6b657dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_indep_prefix_next_singleton

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    IndepFun
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω)
      (X (k + 1)) P := by
  let idx : ({k + 1} : Finset ℕ) := ⟨k + 1, by simp⟩
  have hproj :
      Measurable (fun v : (({k + 1} : Finset ℕ) → ℝ) => v idx) :=
    measurable_pi_apply idx
  have hvector := indep_prefix_next_singleton P X f hM k
  have hcomp := hvector.comp
    (measurable_id : Measurable
      (fun v : ((Finset.Icc 1 k) → ℝ) => v)) hproj
  simpa only [Function.comp_def, id_eq] using hcomp
