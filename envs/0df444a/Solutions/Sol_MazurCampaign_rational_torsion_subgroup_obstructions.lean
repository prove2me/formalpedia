-- Prove2me | solution 1 for MazurCampaign.rational_torsion_subgroup_obstructions
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:39.312215+00:00
-- url     : https://prove2.me/submissions/2c38ca9f-135d-442c-93f3-8871f7cbf6aa

import Theorems.Thm_MazurCampaign_no_two_cube
import Theorems.Thm_MazurCampaign_no_three_square
import Theorems.Thm_MazurCampaign_no_four_square
import Theorems.Thm_MazurCampaign_no_five_square
import Theorems.Thm_MazurCampaign_no_seven_square
import Theorems.Thm_MazurCampaign_no_two_ten
import Theorems.Thm_MazurCampaign_no_two_twelve

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.AvoidsMazurForbiddenSubgroups (MazurCampaign.RationalTorsion E) := by
  exact
    { c2Cube := MazurCampaign.no_two_cube E
      c3Square := MazurCampaign.no_three_square E
      c4Square := MazurCampaign.no_four_square E
      c5Square := MazurCampaign.no_five_square E
      c7Square := MazurCampaign.no_seven_square E
      c2c10 := MazurCampaign.no_two_ten E
      c2c12 := MazurCampaign.no_two_twelve E }

