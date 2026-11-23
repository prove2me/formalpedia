-- Prove2me | solution 1 for GlobalTheory.Kempf.toInter_app_hom_app
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:57.718255+00:00
-- url     : https://prove2.me/submissions/669c8a9b-9f7a-4149-8027-f2b838fd64f5

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
theorem _root_.solution (W : Opens X) (F : X.Sheaf A) (B : Opens X) :
    ((toInter A W).app F).hom.app (op B) = F.obj.map (homOfLE inf_le_left).op := rfl
end GlobalTheory.Kempf
