-- Prove2me | solution 1 for GlobalTheory.SchemeWords.faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:13.962486+00:00
-- url     : https://prove2.me/submissions/ea45f22b-3acc-4196-a2aa-fed38685cd86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver

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
theorem _root_.solution (h : IsCompletedStrictHens A R) : Module.FaithfullyFlat A R :=
  have := h.flat
  Module.FaithfullyFlat.of_flat_of_isLocalHom
end GlobalTheory.SchemeWords
