-- Prove2me | solution 1 for Kyprianou.Ch01.firstNonpositivePrefixSelectedArrivalMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:11:44.587906+00:00
-- url     : https://prove2.me/submissions/7796e80b-30e5-42c9-bbc2-57b20c53c51e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_firstNonpositiveCompoundPrefixIndexMeasurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The arrival time selected by a measurable first nonpositive
mark-prefix length is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (arrival n))
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω =>
      ProbabilityTheory.arrival arrival ((sInf {n : ℕ |
        Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}) - 1) ω) := by
  let N : Ω → ℕ := fun ω =>
    sInf {n : ℕ |
      Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}
  have hN : Measurable N :=
    Kyprianou.Ch01.firstNonpositiveCompoundPrefixIndexMeasurable
      y marks hMarks
  have hPred : Measurable (fun ω : Ω => N ω - 1) :=
    (measurable_of_countable (fun n : ℕ => n - 1)).comp hN
  have hA : Measurable (fun p : Ω × ℕ =>
      ProbabilityTheory.arrival arrival p.2 p.1) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable (fun ω : Ω =>
        ∑ i ∈ Finset.range (n + 1), arrival i ω)
      exact Finset.measurable_sum _ fun i _ => hArrival i
  exact hA.comp (measurable_id.prodMk hPred)
