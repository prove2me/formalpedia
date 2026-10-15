-- Prove2me | solution 2 for NetFeePlatform.InteropDominance.zeta_sub
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:46:40.18597+00:00
-- url     : https://prove2.me/submissions/a4df9bd9-d516-4c18-b3f0-c5631b424ada

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
