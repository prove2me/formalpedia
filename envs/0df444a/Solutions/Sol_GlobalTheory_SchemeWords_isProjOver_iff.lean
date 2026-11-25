-- Prove2me | solution 1 for GlobalTheory.SchemeWords.isProjOver_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:26.812498+00:00
-- url     : https://prove2.me/submissions/7d67ced8-9e25-4c69-aea4-2b514671cb09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
import Theorems.Thm_GlobalTheory_SchemeWords_isProper_of_isProjOver
import Theorems.Thm_GlobalTheory_SchemeWords_isQProjOver_of_isProjOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str


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
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
namespace GlobalTheory.SchemeWords
namespace _root_.GlobalTheory.SchemeWords
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f ∧ IsProper f := by
  refine ⟨fun h => ⟨_root_.GlobalTheory.SchemeWords.isQProjOver_of_isProjOver h, _root_.GlobalTheory.SchemeWords.isProper_of_isProjOver h⟩, ?_⟩
  rintro ⟨⟨N, i, hi, hq, rfl⟩, hp⟩
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  haveI : IsProper i := IsProper.of_comp i (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N)
  exact ⟨N, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, rfl⟩
end _root_.GlobalTheory.SchemeWords
end GlobalTheory.SchemeWords
