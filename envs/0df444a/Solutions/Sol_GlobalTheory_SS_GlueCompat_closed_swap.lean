-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.closed_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:54.781806+00:00
-- url     : https://prove2.me/submissions/dfc84d74-162c-4298-824a-f9b38ff937de

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
theorem _root_.solution {S : Scheme.{0}} {X N G : Over S} {p : X ⟶ N} {q : X ⟶ G}
    (h : IsClosedImmersion (lift p q).left) : IsClosedImmersion (lift q p).left := by
  have : lift q p = lift p q ≫ (β_ N G).hom := by ext <;> simp
  rw [this, Over.comp_left]
  have : IsIso (β_ N G).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ N G).hom))
  infer_instance
end GlobalTheory.SS.GlueCompat
