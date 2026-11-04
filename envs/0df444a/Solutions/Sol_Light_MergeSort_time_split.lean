-- Prove2me | solution 1 for Light.MergeSort.time_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:17.808794+00:00
-- url     : https://prove2.me/submissions/18f3ea8e-6adc-4a9f-ae57-90269af3774f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_WeightedCache3SUM_Alias_b79d9129cb160f6d

set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
namespace Light.MergeSort
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega
end Light.MergeSort
