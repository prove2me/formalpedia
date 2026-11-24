-- Prove2me | solution 1 for GlobalTheory.ChartModel.isClosedImmersion_snd_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:42.309842+00:00
-- url     : https://prove2.me/submissions/00dc9870-9b20-417d-b189-6ea5982893d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart

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
theorem _root_.solution {U Y S : Scheme.{0}} (g : U ⟶ Y) (f : Y ⟶ S) [Mono g]
    [IsSeparated (g ≫ f)] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 _) (Category.comp_id _) (Category.comp_id _))) := by
  have H := pullback_map_diagonal_isPullback g g f
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    H.isoPullback_hom_snd, ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.diagonal g)]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal (g ≫ f)))
  ext : 1 <;> simp
end GlobalTheory.ChartModel
