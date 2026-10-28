-- Prove2me | solution 1 for MarkovProcess.edist_adjacent_lt_of_notMem_finiteGridBadIncrement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:16:11.114421+00:00
-- url     : https://prove2.me/submissions/8efc5f5d-6958-4ce6-a62a-5ce1ecacc4cf

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution
    {N : ℕ} {T : Type*} {X : T → Ω → E} {grid : Fin (N + 1) → T}
    {p : ℝ} (hp : 0 < p) {ε : ℝ≥0∞} {ω : Ω}
    (hω : ω ∉ finiteGridBadIncrement X grid p ε) (i : Fin N) :
    edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) < ε := by
  have h : ¬ ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p := fun h =>
    hω (Set.mem_iUnion.2 ⟨i, h⟩)
  exact (ENNReal.rpow_lt_rpow_iff hp).1 (not_le.1 h)
