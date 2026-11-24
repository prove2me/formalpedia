-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_last_exit_after_finite_downcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:01.523865+00:00
-- url     : https://prove2.me/submissions/51f501c3-6791-4851-b464-1b14555a1bce

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_order
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_le
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_ge
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Order.TypeTags
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      t ≤ l ∧
        lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () =
          ((l-t : ℝ≥0) : WithTop ℝ≥0) := by
  intro Ω X ω y t l ht hl
  exact ⟨p2m810_restart_clock_order Ω X ω y t l ht hl, le_antisymm (p2m810_restart_clock_le Ω X ω y t l ht hl) (p2m810_restart_clock_ge Ω X ω y t l ht hl)⟩
