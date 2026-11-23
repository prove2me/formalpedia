-- Prove2me | solution 2 for GrothendieckPD.Digits.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:16:10.195906+00:00
-- url     : https://prove2.me/submissions/11ba0e4b-fbcf-4d31-9335-5b8c3f94a1ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Theorems.Thm_GrothendieckPD_Digits_theorem_4_1
import Theorems.Thm_GrothendieckPD_Digits_theorem_4_2

/-- Theorem 1.1 (Heilman–Jones–Malavolta, STOC 2027 submission #820, p. 1):
`1.773 ≤ K_G ≤ 1.7799` for the real Grothendieck constant `K_G` of Eq. (1.1). -/
theorem solution :
    (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst ∧
      GrothendieckConstant.grothendieckConst ≤ 17799 / 10000 := by
  constructor
  · exact GrothendieckPD.Digits.theorem_4_1.2
  · have h := GrothendieckPD.Digits.theorem_4_2.2.2.2
    norm_num at h ⊢
    linarith
