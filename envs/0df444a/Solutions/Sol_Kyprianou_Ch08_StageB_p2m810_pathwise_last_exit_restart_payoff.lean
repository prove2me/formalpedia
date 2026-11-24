-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_pathwise_last_exit_restart_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:52:31.149108+00:00
-- url     : https://prove2.me/submissions/73e38cbb-d392-49b4-8202-585bb02554cd

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_positive_start_down_clock_pos
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_no_downcrossing_last_exit_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_drift_finite_last_exit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_after_finite_downcrossing
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Complex.Exponential
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (y : ℝ) (q : ℝ) (hy : 0 < y) (h0 : f 0 = 0)
    (hc : ContinuousWithinAt f (Ici 0) 0) (h : Tendsto f atTop atTop) :
    discountedPositiveLastExit (fun t (_ : Unit) => f t) q y () =
      WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) *
          discountedAt q (lastNegativeVisit (fun s (_ : Unit) => y + f (t+s)) ()))
        (tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 ()) := by
  let X : ℝ≥0 → Unit → ℝ := fun t _ => f t
  let T := tauMinus (shifted X y) 0 ()
  let L := lastExitShifted X y ()
  have htpos : 0 < T := p2m810_positive_start_down_clock_pos f y hy h0 hc
  change (if 0 < L then discountedAt q L else 0) = _
  by_cases ht : T = ⊤
  · have hl : L = 0 := p2m810_no_downcrossing_last_exit_zero f y ht
    simp [hl,show tauMinus (shifted X y) 0 () = ⊤ from ht,T,X]
  · obtain ⟨t,he⟩ := WithTop.ne_top_iff_exists.mp ht
    obtain ⟨l,hl⟩ := WithTop.ne_top_iff_exists.mp (p2m810_drift_finite_last_exit f y h)
    have hL : L = (l : WithTop ℝ≥0) := hl.symm
    have hT : T = (t : WithTop ℝ≥0) := he.symm
    obtain ⟨htl,hr⟩ := p2m810_last_exit_after_finite_downcrossing Unit X () y t l hT hL
    rw [hT] at htpos
    have hlpos : 0 < L := by rw [hL]; exact htpos.trans_le (WithTop.coe_le_coe.mpr htl)
    rw [if_pos hlpos,hL]
    change discountedAt q (l : WithTop ℝ≥0) =
      WithTop.recTopCoe (0 : ℝ) _ T
    rw [hT]
    simp only [WithTop.recTopCoe_coe]
    change Real.exp (-q * (l : ℝ)) = _ * discountedAt q
      (lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ()) ())
    rw [hr]
    simp only [discountedAt,NNReal.coe_sub htl,← Real.exp_add]
    congr 1
    ring
