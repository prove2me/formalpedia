-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.affine_flow_integral_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:11:17.428062+00:00
-- url     : https://prove2.me/submissions/e4226b64-e41f-4690-b191-b7100bea9334
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalB_sum
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalR_closed
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalL_interior

open MultiwayGap2325.Main.Supplement

theorem solution (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    totalB T (affineData q T).weighting = affineBSum q T ∧
    totalR T (affineData q T) = affineRClosed q T ∧
    totalL T (affineData q T).weighting =
      (1 - T) * totalB T (affineData q T).weighting + affineInteriorClosed q T := by
  exact ⟨affine_totalB_sum q hq T hT0 hT1,
    affine_totalR_closed q hq T hT0 hT1,
    affine_totalL_interior q hq T hT0 hT1⟩
