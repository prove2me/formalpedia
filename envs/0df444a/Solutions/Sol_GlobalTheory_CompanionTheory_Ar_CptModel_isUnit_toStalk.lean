-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.isUnit_toStalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:38.356173+00:00
-- url     : https://prove2.me/submissions/ef49ce02-6b1a-46bc-87e3-45d58369eb68

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
variable {R K : Type} [CommRing R] [Field K]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution (p : PrimeSpectrum R) {s : R} (hs : s ∉ p.asIdeal) :
    IsUnit (tS p s) :=
  IsLocalization.map_units (M := p.asIdeal.primeCompl)
    ((Spec.structureSheaf R).presheaf.stalk p) ⟨s, hs⟩
end GlobalTheory.CompanionTheory.Ar.CptModel
