-- Prove2me | solution 1 for GlobalTheory.Kempf.exists_isBasis_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:46.439244+00:00
-- url     : https://prove2.me/submissions/0faf2e0d-9efd-461f-8e6a-80e3061dd1ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
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
namespace GlobalTheory.Kempf
theorem _root_.solution (hS : S.ShortExact) {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    {V : Opens X} (s : S.X₃.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧ ∃ t : S.X₂.obj.obj (op (V ⊓ W)),
      S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s := by
  obtain ⟨U, hUV, ⟨t, ht⟩, hxU⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g) V s x hx
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 h𝔅 hxU
  have hle : V ⊓ W ≤ U := inf_le_right.trans hWU
  refine ⟨W, hW, hxW, hWU.trans hUV, S.X₂.obj.map (homOfLE hle).op t, ?_⟩
  refine (ConcreteCategory.congr_hom (S.g.hom.naturality (homOfLE hle).op) t).trans ?_
  refine (congrArg (S.X₃.obj.map (homOfLE hle).op) ht).trans ?_
  exact (ConcreteCategory.congr_hom
    (S.X₃.obj.map_comp (homOfLE hUV).op (homOfLE hle).op) s).symm
end GlobalTheory.Kempf
