-- Prove2me | solution 1 for Light.Seg.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:18.944695+00:00
-- url     : https://prove2.me/submissions/887cbc40-2bd0-499b-83e0-576b60a6991f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_Light_Seg_of_sameOn


set_option autoImplicit false
section
open Light
open ThreeSumApsp
namespace Light
namespace Seg
theorem _root_.solution {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : Seg μ a l) (hk : Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega
end Seg
end Light
