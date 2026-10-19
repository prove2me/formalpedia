-- Prove2me | solution 1 for IntMul.Kappa.openai_round6_small_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:35:59.929392+00:00
-- url     : https://prove2.me/submissions/647f7ffa-a970-4f20-aff3-f921362a73ea

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_hist_moment_le_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul.Kappa

theorem solution :
    histMoment Jain.bitR6 529 (1 - (1 : ℝ) / 10 ^ 7) < 148225616 ∧
    histMoment Jain.cxR6 576 (1 - (1 : ℝ) / 10 ^ 7) < 207387136 := by
  constructor
  · have hbound :=
      hist_moment_le_linear Jain.bitR6 529 (1 / (10 : ℝ) ^ 7)
        (by norm_num) (by norm_num)
    apply lt_of_le_of_lt hbound
    norm_num [Jain.bitR6]
  · have hbound :=
      hist_moment_le_linear Jain.cxR6 576 (1 / (10 : ℝ) ^ 7)
        (by norm_num) (by norm_num)
    apply lt_of_le_of_lt hbound
    norm_num [Jain.cxR6]
