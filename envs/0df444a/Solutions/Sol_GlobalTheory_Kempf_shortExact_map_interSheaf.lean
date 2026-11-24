-- Prove2me | solution 1 for GlobalTheory.Kempf.shortExact_map_interSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:47.196839+00:00
-- url     : https://prove2.me/submissions/06112ded-08b5-47fc-9968-a9f687b372ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_exact_map_interSheaf

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
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅)
    (hsurj : ∀ B ∈ 𝔅, Function.Surjective (S.g.hom.app (op B))) {W : Opens X} (hW : W ∈ 𝔅) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).ShortExact := by
  refine ShortComplex.ShortExact.mk' (exact_map_interSheaf hS W).1 (exact_map_interSheaf hS W).2 ?_
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
    ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t x hx ↦ ?_)
  obtain ⟨B, hB, hxB, hBU⟩ := Opens.isBasis_iff_nbhd.1 h𝔅 hx
  exact ⟨B, hBU, hsurj (B ⊓ W) (hinf B hB W hW) _, hxB⟩
end GlobalTheory.Kempf
