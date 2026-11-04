-- Prove2me | solution 1 for Light.MergeSort.sorted_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:30.529708+00:00
-- url     : https://prove2.me/submissions/bb6fcbf6-1e11-40ec-b26b-d11b3d54b2b4

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl


set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
namespace Light.MergeSort
theorem _root_.solution {μ : ℕ → ℤ} {a fr : ℕ} {L : List ℤ} (hseg : Seg μ a L) (hL : L.length ≤ 1) :
    Sorted μ a fr L μ := by
  refine ⟨⟨L, hseg, .refl _, ?_⟩, .refl⟩
  match L, hL with
  | [], _ => exact .nil
  | [x], _ => exact List.pairwise_singleton _ _
end Light.MergeSort
