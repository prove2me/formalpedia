-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.affine_flow_validity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:08:22.535017+00:00
-- url     : https://prove2.me/submissions/63af0bb6-3864-4271-a28f-63d34817a2c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_regular
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_capacity
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_terminal
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_conservation

open MultiwayGap2325.Main.Supplement

theorem solution (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    IsFlowInstance T (affineData q T) := by
  exact ⟨affine_regular q hq T hT0 hT1,
    affine_capacity q hq T hT0 hT1,
    affine_terminal q hq T hT0 hT1,
    affine_conservation q hq T hT0 hT1⟩
