-- Prove2me | solution 1 for GlobalTheory.SchemeWords.injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:54.766084+00:00
-- url     : https://prove2.me/submissions/5771a163-a067-420e-b802-815faee99ed9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
import Theorems.Thm_GlobalTheory_SchemeWords_faithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SchemeWords
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
  [Algebra A R] [IsLocalHom (algebraMap A R)]
namespace GlobalTheory.SchemeWords
theorem _root_.solution (h : IsCompletedStrictHens A R) : Function.Injective (algebraMap A R) :=
  have := faithfullyFlat h
  FaithfulSMul.algebraMap_injective A R
end GlobalTheory.SchemeWords
