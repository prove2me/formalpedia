-- Prove2me | solution 1 for NetFeePlatform.InteropDominance.zeta_sub
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:45:20.377651+00:00
-- url     : https://prove2.me/submissions/7b83934b-62c0-4a12-9b88-f6d3c84ed1f8

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropDominance_Zeta
open NetFeePlatform.InteropDominance

theorem solution(γ lamLo lamHi n : ℝ) (hγ : 0 < γ) (hlt : lamLo < lamHi) (hn : 1 / 2 < n) :
    zeta γ lamLo n - zeta γ lamHi n = 2 * γ * (lamLo - lamHi) * (2 * n - 1) ∧
    zeta γ lamLo n - zeta γ lamHi n < 0 := by
  have h : zeta γ lamLo n - zeta γ lamHi n = 2 * γ * (lamLo - lamHi) * (2 * n - 1) := by
    unfold zeta; ring
  refine ⟨h, ?_⟩
  rw [h]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)
