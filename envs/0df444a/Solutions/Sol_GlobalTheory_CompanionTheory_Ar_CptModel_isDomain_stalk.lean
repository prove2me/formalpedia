-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.isDomain_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:25.653504+00:00
-- url     : https://prove2.me/submissions/313715e0-7450-4739-8101-9bfeaaf89560

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
theorem _root_.solution {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) :=
  Function.Injective.isDomain (genMap ξ p) (h.inj p)
end GlobalTheory.CompanionTheory.Ar.CptModel
