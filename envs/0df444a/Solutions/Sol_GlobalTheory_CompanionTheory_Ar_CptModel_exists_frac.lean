-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.exists_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:38.029516+00:00
-- url     : https://prove2.me/submissions/a4fe191f-86b5-4e57-9b49-eae6207847f3

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
theorem _root_.solution (φ : R →+* K) (p : Cpt (pt φ)) (x : (Spec (CommRingCat.of R)).presheaf.stalk p.1) :
    ∃ a s : R, s ∉ p.1.asIdeal ∧
      x * tS p.1 s = tS p.1 a := by
  have key : ∀ (q : PrimeSpectrum R) (y : (Spec.structureSheaf R).presheaf.stalk q), ∃ a s : R, s ∉ q.asIdeal ∧
      y * algebraMap R _ s = algebraMap R _ a := fun q y => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.asIdeal.primeCompl y
    exact ⟨a, s, s.2, h⟩
  exact key p.1 x
end GlobalTheory.CompanionTheory.Ar.CptModel
