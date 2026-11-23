-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonArrivalShiftAdditive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:05:13.012579+00:00
-- url     : https://prove2.me/submissions/4687f1f2-4b4b-4522-9d24-f65e1864de5a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    {Ω : Type*} (arrival : ℕ → Ω → ℝ)
    (w : Ω) (n : ℕ) :
    ProbabilityTheory.arrival arrival (n + 1) w =
      arrival 0 w +
        ProbabilityTheory.arrival (fun i v => arrival (i + 1) v) n w := by
  simp only [ProbabilityTheory.arrival]
  convert (Finset.sum_range_add
    (fun i : ℕ => arrival i w) 1 (n + 1)) using 1 <;>
    simp [Nat.add_comm]
