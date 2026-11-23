-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.explicit_flow_instance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:02.231679+00:00
-- url     : https://prove2.me/submissions/413d992e-fa54-43f4-ab39-cc2cf60c6846
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_instances
import Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_shape

open MultiwayGap2325.Main.Supplement

noncomputable section

theorem solution :
    ∃ D : FlowData 10, IsFlowInstance (3 / 5) D ∧
      HasAffineLabelFlows (3 / 5) D ∧ HasConstantWeights (3 / 5) D ∧
      0 < totalL (3 / 5) D.weighting ∧
      (totalB (3 / 5) D.weighting - totalR (3 / 5) D) / totalL (3 / 5) D.weighting =
        (9999320418500 : ℝ) / 8180229294583 := by
  obtain ⟨hvalid, hBS, hBC, hR, hNet, hL⟩ :=
    affine_flow_instances 10 (by norm_num) (3 / 5) (by norm_num) (by norm_num)
  obtain ⟨haffine, hconstant⟩ := affine_flow_shape 10 (3 / 5)
  have hLval : totalL (3 / 5) (affineData 10 (3 / 5)).weighting =
      (8180229294583 : ℝ) / 16665989760000 := by
    rw [hL, hBC]
    norm_num [affineBClosed, affineZ, affineInteriorClosed, Nat.factorial,
      Finset.sum_Icc_succ_top]
  refine ⟨affineData 10 (3 / 5), hvalid, haffine, hconstant, ?_, ?_⟩
  · rw [hLval]
    norm_num
  · rw [hNet, hLval]
    norm_num [affineNetClosed, Nat.factorial]
