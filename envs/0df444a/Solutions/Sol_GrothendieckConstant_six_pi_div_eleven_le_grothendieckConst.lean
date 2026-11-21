-- Prove2me | solution 1 for GrothendieckConstant.six_pi_div_eleven_le_grothendieckConst
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:49:35.914209+00:00
-- url     : https://prove2.me/submissions/f9ba05fb-a021-47ec-b5bb-99e381c0b225
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Theorems.Thm_GrothendieckPD_Digits_theorem_4_1

namespace GrothendieckConstant

theorem _root_.solution :
    6 * Real.pi / 11 ≤ grothendieckConst := by
  have h1 : 6 * Real.pi / 11 ≤ (1773 / 1000 : ℝ) := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    linarith
  have h2 : (1773 / 1000 : ℝ) ≤ grothendieckConst := by
    have := GrothendieckPD.Digits.theorem_4_1.2
    simpa using this
  linarith

end GrothendieckConstant
