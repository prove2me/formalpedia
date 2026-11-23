-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.rounded_certificate_totals
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:17.848341+00:00
-- url     : https://prove2.me/submissions/814fe1bb-d8ab-4c79-9abe-c360b7fbf701

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

/-- The scalar totals printed in equation (39) for the external rounded table. -/
theorem solution :
    let B : ℝ := (1725000000167 : ℝ) / 1725000000000
    let R : ℝ := (2593033 : ℝ) / 910800000000000
    let L : ℝ := (43107286191734959 : ℝ) / 53130000000000000
    0 < L ∧ (B - R) / L = MultiwayGap2325.Main.beta := by
  norm_num [MultiwayGap2325.Main.beta]
