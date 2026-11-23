-- Prove2me | solution 1 for Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:59:37.865887+00:00
-- url     : https://prove2.me/submissions/62c03535-ea7d-46cb-a61c-27f24f2d0d17

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω)
    (hBefore : (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω) :
    integerCompoundPoisson y arrival marks t ω = (y : ℤ) := by
  have hNoJump :=
    AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
      arrival marks (t : ℝ) ω hBefore
  simp [integerCompoundPoisson, hNoJump]

