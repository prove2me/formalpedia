-- Prove2me | solution 1 for GlobalTheory.SchemeWords.isProper_of_isProjOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:24.747305+00:00
-- url     : https://prove2.me/submissions/78652b86-5830-40fe-8f9e-84504dafc409

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_projProper


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
theorem _root_.solution (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : IsProper f :=
  _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper R X f h
end _root_.GlobalTheory.SchemeWords
end GlobalTheory.SchemeWords
