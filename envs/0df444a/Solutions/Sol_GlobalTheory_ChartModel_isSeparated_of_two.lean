-- Prove2me | solution 1 for GlobalTheory.ChartModel.isSeparated_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:31.386109+00:00
-- url     : https://prove2.me/submissions/30f35b2c-8ee8-48af-8823-19324b3a7c8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
import Theorems.Thm_GlobalTheory_ChartModel_isClosedImmersion_snd_diagonal

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
open GlobalTheory GlobalTheory.ChartModel
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ChartModel
theorem _root_.solution {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (twoCover
    (pullback.map (u ≫ f) (u ≫ f) f f u u (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    (pullback.map (v ≫ f) (v ≫ f) f f v v (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ?_) ?_
  · intro z
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
    exact h _ _ (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  · rintro (_ | _)
    · exact isClosedImmersion_snd_diagonal u f
    · exact isClosedImmersion_snd_diagonal v f
end GlobalTheory.ChartModel
