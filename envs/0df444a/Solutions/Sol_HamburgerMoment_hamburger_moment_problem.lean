-- Prove2me | solution 1 for HamburgerMoment.hamburger_moment_problem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:15:37.623404+00:00
-- url     : https://prove2.me/submissions/83b72df8-3d3b-47a1-8e78-92bc9120c13d

import Theorems.Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence
import Theorems.Thm_HamburgerMoment_isMomentSequence_of_hankelPosDef

set_option autoImplicit false

theorem solution (m : ℕ → ℝ) :
    HamburgerMoment.IsMomentSequence m ↔ HamburgerMoment.HankelPosDef m := by
  constructor
  · exact HamburgerMoment.hankelPosDef_of_isMomentSequence m
  · exact HamburgerMoment.isMomentSequence_of_hankelPosDef m
