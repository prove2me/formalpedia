-- Prove2me | solution 1 for GlobalTheory.Kempf.toInter_app_comp_map_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:48.15586+00:00
-- url     : https://prove2.me/submissions/9fdaee78-1c4e-4f50-96e9-fce256ed9312

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
theorem _root_.solution (W : Opens X) {F G : X.Sheaf A} (f : F ⟶ G)
    [IsIso ((toInter A W).app G)] :
    (toInter A W).app F ≫ (interSheaf A W).map f ≫ inv ((toInter A W).app G) = f := by
  rw [← (toInter A W).naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl
end GlobalTheory.Kempf
