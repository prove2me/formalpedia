-- Prove2me | solution 2 for NetFeePlatform.Competition.gChar_three_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:46:41.761746+00:00
-- url     : https://prove2.me/submissions/3012cbdc-2119-49c4-ade1-cddf467a89b0

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
