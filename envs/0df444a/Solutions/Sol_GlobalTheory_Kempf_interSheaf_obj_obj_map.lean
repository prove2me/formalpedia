-- Prove2me | solution 1 for GlobalTheory.Kempf.interSheaf_obj_obj_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.645805+00:00
-- url     : https://prove2.me/submissions/08737aac-6d8d-489f-8143-0a4b179b0964

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable (A : Type u') [Category.{v'} A]
variable {A}
namespace GlobalTheory.Kempf
theorem _root_.solution (W : Opens X) (F : X.Sheaf A) {B B' : Opens X}
    (i : B' ⟶ B) : ((interSheaf A W).obj F).obj.map i.op =
      F.obj.map (homOfLE (inf_le_inf_right W i.le)).op := rfl
end GlobalTheory.Kempf
