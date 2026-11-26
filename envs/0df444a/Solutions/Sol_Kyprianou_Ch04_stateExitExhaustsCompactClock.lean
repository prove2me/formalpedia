-- Prove2me | solution 1 for Kyprianou.Ch04.stateExitExhaustsCompactClock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:11.017699+00:00
-- url     : https://prove2.me/submissions/4fb3835b-1c37-4ced-8a30-68ed920da2e0

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Increasing spatial exit clocks exhaust each compact time horizon of a cadlag path. -/
theorem solution (Y : NNReal → ℝ) (hY : IsCadlag Y) (T : NNReal) :
    ∃ n : ℕ, (T : WithTop NNReal) <
      sInf {v : WithTop NNReal | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |Y u|} := by
  obtain ⟨A,hA⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 Y hY 1 (T+1)
  obtain ⟨B,hB⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 Y hY (-1) (T+1)
  obtain ⟨n,hn⟩ := exists_nat_ge (max A B)
  refine ⟨n,lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by simp : T < T+1)) (le_sInf ?_)⟩
  rintro v ⟨u,rfl,hu⟩
  apply WithTop.coe_le_coe.mpr
  by_contra h
  have hm : u ∈ Icc (0 : NNReal) (T+1) := ⟨zero_le,le_of_lt (lt_of_not_ge h)⟩
  have ha := hA (mem_image_of_mem (fun s => (1:ℝ)*Y s) hm)
  have hb := hB (mem_image_of_mem (fun s => (-1:ℝ)*Y s) hm)
  simp only [one_mul] at ha
  simp only [neg_mul,one_mul] at hb
  exact (not_le_of_gt hu) (abs_le.mpr ⟨by linarith [le_max_right A B],ha.trans ((le_max_left A B).trans hn)⟩)
