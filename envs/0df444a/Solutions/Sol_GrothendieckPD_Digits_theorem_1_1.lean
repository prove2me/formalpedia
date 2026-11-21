-- Prove2me | solution 1 for GrothendieckPD.Digits.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:49:26.570172+00:00
-- url     : https://prove2.me/submissions/7c74cc51-e0e5-4a5b-8676-075c11c31057
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Theorems.Thm_GrothendieckPD_Digits_theorem_4_1
import Theorems.Thm_GrothendieckPD_Digits_theorem_4_2

namespace GrothendieckPD.Digits

theorem _root_.solution :
    (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst ∧
      GrothendieckConstant.grothendieckConst ≤ 17799 / 10000 := by
  have h1 := theorem_4_1
  have h2 := theorem_4_2
  refine ⟨h1.2, ?_⟩
  have hlt := h2.2.2.2
  have hle : GrothendieckConstant.grothendieckConst ≤ 1779893 / 1000000 := le_of_lt hlt
  have hw : (1779893 / 1000000 : ℝ) ≤ 17799 / 10000 := by norm_num
  linarith

end GrothendieckPD.Digits
