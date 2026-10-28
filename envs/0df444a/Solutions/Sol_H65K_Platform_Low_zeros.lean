-- Prove2me | solution 1 for H65K.Platform.Low.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:24:12.662257+00:00
-- url     : https://prove2.me/submissions/c76a5443-cdae-479a-8bc7-21acb6852c81

import Theorems.Thm_H65K_Platform_LowGroup000_zeros
import Theorems.Thm_H65K_Platform_LowGroup001_zeros
import Theorems.Thm_H65K_Platform_LowGroup002_zeros
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution : RS5.BandZeros ((65573390 : ℝ) / 65536) ((721160233 : ℝ) / 65536) 10680 := by
  have h0 := H65K.Platform.LowGroup000.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K.Platform.LowGroup001.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K.Platform.LowGroup002.zeros
  exact h2
