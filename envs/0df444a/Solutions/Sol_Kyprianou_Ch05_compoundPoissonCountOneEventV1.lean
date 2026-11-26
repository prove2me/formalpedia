-- Prove2me | solution 1 for Kyprianou.Ch05.compoundPoissonCountOneEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:08:40.973232+00:00
-- url     : https://prove2.me/submissions/664ce7b8-f241-4cd2-a026-6062c8cd4a29

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex
theorem solution
    (T : ℕ → ℝ) (t : ℝ) :
    LevyFoundations.jumpCount T t = 1 ↔ T 0 ≤ t ∧ t < T 1 := by
  classical
  let S : Set ℕ := {n | t < T n}
  change sInf S = 1 ↔ T 0 ≤ t ∧ t < T 1
  constructor
  · intro h
    have hm := Nat.sInf_mem (Nat.nonempty_of_sInf_eq_succ h)
    rw [h] at hm
    have hn := Nat.notMem_of_lt_sInf (show 0 < sInf S by rw [h]; decide)
    exact ⟨le_of_not_gt (fun hlt => hn hlt),hm⟩
  · intro h
    have hm : 1 ∈ S := h.2
    have hle := Nat.sInf_le hm
    have hn : sInf S ≠ 0 := by
      intro hz
      rcases Nat.sInf_eq_zero.mp hz with h0 | hEmpty
      · exact (not_lt_of_ge h.1) h0
      · rw [hEmpty] at hm; exact hm
    omega
