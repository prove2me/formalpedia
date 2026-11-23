-- Prove2me | solution 1 for GlobalTheory.Kempf.interSheaf_map_hom_app
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.128097+00:00
-- url     : https://prove2.me/submissions/97b129d6-837e-4c22-873b-b4f6a3edf8f5

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
theorem _root_.solution (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G) (B : Opens X) :
    ((interSheaf A W).map f).hom.app (op B) = f.hom.app (op (B ⊓ W)) := rfl
end GlobalTheory.Kempf
