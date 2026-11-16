-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanism_continuousOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:09:43.849453+00:00
-- url     : https://prove2.me/submissions/24b86d47-ed56-4693-8e0f-a35afa068542

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingMechanism_continuousOn_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem solution (rate : ℝ) (offspring : PMF ℕ) :
    ContinuousOn (branchingMechanism rate offspring) (Ioi (0 : ℝ)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxpos : 0 < x := hx
  have hlocal :=
    Kyprianou.Ch01.branchingMechanism_continuousOn_Icc
      rate offspring (x / 2) (x + 1)
      (by linarith) (by linarith)
  exact hlocal.continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))
