-- Prove2me | solution 1 for Light.triPre_of_arrays
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:55.783221+00:00
-- url     : https://prove2.me/submissions/348154bb-82f9-40a9-ae2f-c3a0f79120a6

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
theorem _root_.solution {n U base : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n))) :
    (⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩ : TriInst).Pre μ
      (base + 3 * (n * n)) :=
  ⟨hn, hU, hAB.len, hBC.len, hAC.len, hAB.seg, hBC.seg, hAC.seg, hAB.bound, hBC.bound, hAC.bound,
    hAB.below, hBC.below, hAC.below⟩
end Light
