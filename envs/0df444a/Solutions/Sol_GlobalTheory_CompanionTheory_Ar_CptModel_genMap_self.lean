-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.genMap_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:38.189491+00:00
-- url     : https://prove2.me/submissions/f0b43226-8056-4141-a58c-97c1f44d8232

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    genMap ξ (self ξ) = (Scheme.stalkClosedPointTo ξ).hom := by
  have h : X.presheaf.stalkSpecializes (self ξ).2 = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  rw [h]
  rfl
end GlobalTheory.CompanionTheory.Ar.CptModel
