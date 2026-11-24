-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.regAt_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:47.742334+00:00
-- url     : https://prove2.me/submissions/9500378f-2988-4a24-8a55-ece88823a9ee

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_genMap_push

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩
end GlobalTheory.CompanionTheory.Ar.ProjCoord
