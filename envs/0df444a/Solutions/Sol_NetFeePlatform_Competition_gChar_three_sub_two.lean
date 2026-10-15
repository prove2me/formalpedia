-- Prove2me | solution 1 for NetFeePlatform.Competition.gChar_three_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:45:20.501598+00:00
-- url     : https://prove2.me/submissions/f55c348c-5b2e-4ee7-94f5-f9f7b3b84a92

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar
open NetFeePlatform.Competition

theorem solution(γ n : ℝ) (hn0 : 0 < n) (hn1 : n < 1) :
    gChar γ 3 n - gChar γ 2 n = -Real.log 2 + 1 / (1 - n / 2) - 1 / (1 - n) + γ * n := by
  unfold gChar
  have h1 : (1:ℝ) - n ≠ 0 := by linarith
  norm_num
  ring
