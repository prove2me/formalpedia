-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.target_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:06.409789+00:00
-- url     : https://prove2.me/submissions/e8607cbf-4b87-45b4-9028-b646711d4945

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
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {X Y U V U' V' : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ Y} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : Y, x ∈ Set.range u ∨ x ∈ Set.range v) {a : U' ⟶ X} {b : U' ⟶ U} {c : V' ⟶ X} {d : V' ⟶ V}
    (h₁ : IsPullback a b f u) (h₂ : IsPullback c d f v) (hb : P b) (hd : P d) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (coverTwo u v hc) ?_
  rintro (_ | _)
  · change P (pullback.snd f u)
    rwa [← h₁.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  · change P (pullback.snd f v)
    rwa [← h₂.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
end GlobalTheory.SS.GlueCompat
