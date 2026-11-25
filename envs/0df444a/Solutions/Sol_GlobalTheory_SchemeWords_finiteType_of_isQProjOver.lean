-- Prove2me | solution 1 for GlobalTheory.SchemeWords.finiteType_of_isQProjOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:29.944416+00:00
-- url     : https://prove2.me/submissions/9c138efd-dcaa-468a-a5a4-5ee205ef0caa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_IsQProjOverOfIsProjOver
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
namespace GlobalTheory.SchemeWords
theorem _root_.solution (h : IsQProjOver f) :
    LocallyOfFiniteType f ∧ QuasiCompact f ∧ IsSeparated f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.SchemeWords
