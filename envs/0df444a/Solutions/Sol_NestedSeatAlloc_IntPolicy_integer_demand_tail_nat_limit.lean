-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.integer_demand_tail_nat_limit
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:18:29.906211+00:00
-- url     : https://prove2.me/submissions/7709c585-5d0f-4141-9351-eddb7a263859

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) :
    Tendsto (fun n : ℕ => P.real {ω | (n : ℝ) < X 1 ω}) atTop (𝓝 0) := by
  letI := hM.isProb
  let E : ℕ → Set Ω := fun n => {ω | (n : ℝ) < X 1 ω}
  have hm : ∀ n, NullMeasurableSet (E n) P := fun n =>
    ((hM.meas 1) measurableSet_Ioi).nullMeasurableSet
  have ha : Antitone E := by
    intro n m hnm ω hω
    change (m : ℝ) < X 1 ω at hω
    change (n : ℝ) < X 1 ω
    exact lt_of_le_of_lt (Nat.cast_le.mpr hnm) hω
  have he : (⋂ n, E n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨n, hn⟩ := hint 1 ω
    have h := Set.mem_iInter.mp hω n
    change (n : ℝ) < X 1 ω at h
    simpa [hn] using h
  have h := tendsto_measure_iInter_atTop hm ha ⟨0, measure_ne_top P _⟩
  rw [he, measure_empty] at h
  simpa [Measure.real, Function.comp_def, E] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

#print axioms solution
