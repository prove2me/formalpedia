-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.pb_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:09.890438+00:00
-- url     : https://prove2.me/submissions/cfb7086a-7a8b-4d41-99c5-d560e3a5fd97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution {A X Y : Scheme.{0}} {a : A ⟶ X} {i : X ⟶ Y} [Mono i] {j : A ⟶ Y} (h : a ≫ i = j) :
    IsPullback a (𝟙 A) i j := by
  subst h
  exact IsPullback.of_vert_isIso_mono (by constructor; simp)
end GlobalTheory.SS.GlueCompat
