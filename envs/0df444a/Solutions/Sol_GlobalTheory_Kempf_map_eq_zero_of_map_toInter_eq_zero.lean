-- Prove2me | solution 1 for GlobalTheory.Kempf.map_eq_zero_of_map_toInter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:07.370407+00:00
-- url     : https://prove2.me/submissions/53ccc222-d3ec-4641-b776-f20551d39728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_toInter_app_comp_map_comp_inv
import Theorems.Thm_GlobalTheory_SheafLES_map_comp


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
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES
namespace GlobalTheory.Kempf
theorem _root_.solution {W : Opens X} {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) [IsIso ((toInter AddCommGrpCat.{u} W).app G)] {n : ℕ} {V : Opens X}
    {α : Sheaf.H'.{w} F n V} (h : map.{w} ((toInter AddCommGrpCat.{u} W).app F) n V α = 0) :
    map.{w} f n V α = 0 := by
  refine (congrArg (fun g ↦ map.{w} g n V α) (toInter_app_comp_map_comp_inv W f).symm).trans ?_
  refine (map_comp _ _ n V α).trans ?_
  exact (congrArg _ h).trans (map_zero _)
end GlobalTheory.Kempf
