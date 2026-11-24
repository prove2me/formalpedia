-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_no_downcrossing_last_exit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:01:40.594818+00:00
-- url     : https://prove2.me/submissions/1d0ade50-3e41-44a3-89a6-37da14b0e90e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (y : ℝ) (h : tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 () = ⊤) :
    lastExitShifted (fun t (_ : Unit) => f t) y () = 0 := by
  let S : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + f u < 0}
  change sInf S = ⊤ at h
  have he : S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨u,hu,rfl,hneg⟩
    have hh := sInf_le (show (u : WithTop ℝ≥0) ∈ S from ⟨u,hu,rfl,hneg⟩)
    rw [h] at hh
    exact (not_le_of_gt (WithTop.coe_lt_top u)) hh
  change sSup S = 0
  simp [he]
