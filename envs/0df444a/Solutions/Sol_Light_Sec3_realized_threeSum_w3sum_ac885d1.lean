-- Prove2me | solution 1 for Light.Sec3.realized_threeSum_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:21.338267+00:00
-- url     : https://prove2.me/submissions/266a94f5-4c86-42d7-bd0a-b906e467a155

import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_WeightedCache3SUM_Alias_7945670abe02dea3


set_option autoImplicit false
section
open Light Light.Sec3
open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec
namespace Light.Sec3
theorem _root_.solution (T : ℕ → ℝ → ℝ) (h : SolvedIn s3Task T) :
    Realized EndStatement.ThreeSum T :=
  wrap3Sum.realized h
end Light.Sec3
