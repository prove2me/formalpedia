-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.affine_flow_instances
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:19:53.872409+00:00
-- url     : https://prove2.me/submissions/36cdc829-489d-454f-b5a1-f82780cb92a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_validity
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_integral_values
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_closed_form_algebra

open MultiwayGap2325.Main.Supplement

theorem solution (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    let D := affineData q T
    IsFlowInstance T D ∧
    totalB T D.weighting = affineBSum q T ∧
    totalB T D.weighting = affineBClosed q T ∧
    totalR T D = affineRClosed q T ∧
    totalB T D.weighting - totalR T D = affineNetClosed q T ∧
    totalL T D.weighting = (1 - T) * totalB T D.weighting + affineInteriorClosed q T := by
  dsimp only
  have hD := affine_flow_validity q hq T hT0 hT1
  have hvals := affine_flow_integral_values q hq T hT0 hT1
  have halg := affine_closed_form_algebra q hq T hT0 hT1
  obtain ⟨hB, hR, hL⟩ := hvals
  refine ⟨hD, hB, hB.trans halg.1, hR, ?_, hL⟩
  rw [hB, halg.1, hR]
  exact halg.2
