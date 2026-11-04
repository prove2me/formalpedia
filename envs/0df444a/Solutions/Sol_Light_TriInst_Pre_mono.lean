-- Prove2me | solution 1 for Light.TriInst.Pre.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:09.567299+00:00
-- url     : https://prove2.me/submissions/ad67700e-d4a3-4191-a16a-70f9983870e4

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks

set_option autoImplicit false
section
open ThreeSumApsp
open Light
open ThreeSumApsp.Spec
namespace Light
namespace TriInst.Pre
theorem _root_.solution {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowAB := h.belowAB.trans hfr
    belowBC := h.belowBC.trans hfr
    belowAC := h.belowAC.trans hfr }
end TriInst.Pre
end Light
