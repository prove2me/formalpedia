-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDuality_finiteExtremaAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:26:54.207224+00:00
-- url     : https://prove2.me/submissions/2dcda0da-8ac2-49d1-864d-22feff6bee18

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Translation and negation of finite extrema. -/
theorem solution
    {ι : Type} [Finite ι] [Nonempty ι] (v : ι → ℝ) (c : ℝ) :
    sSup (Set.range (fun i => v i - c)) = sSup (Set.range v) - c ∧
    sSup (Set.range (fun i => -v i)) = -sInf (Set.range v) := by
  constructor
  · apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      have h := le_csSup (Set.finite_range v).bddAbove (Set.mem_range_self i)
      linarith
    · have h : sSup (Set.range v) ≤
          sSup (Set.range (fun i => v i - c)) + c := by
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨i, rfl⟩
        have hi := le_csSup (Set.finite_range (fun i => v i - c)).bddAbove
          (Set.mem_range_self i)
        linarith
      linarith
  · apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      have h := csInf_le (Set.finite_range v).bddBelow (Set.mem_range_self i)
      linarith
    · have h : -sSup (Set.range (fun i => -v i)) ≤ sInf (Set.range v) := by
        apply le_csInf (Set.range_nonempty _)
        rintro _ ⟨i, rfl⟩
        have hi := le_csSup (Set.finite_range (fun i => -v i)).bddAbove
          (Set.mem_range_self i)
        linarith
      linarith
