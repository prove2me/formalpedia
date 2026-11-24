-- Prove2me | solution 1 for GlobalTheory.GenericHom.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:05.26024+00:00
-- url     : https://prove2.me/submissions/f7b51ecd-db10-472b-9cf9-25a4bf10da87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension

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
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]
omit [IsAlgClosed k]
namespace GlobalTheory.GenericHom
theorem _root_.solution {U H Z : Over (Sp k)} (j : U ⟶ H) [IsOpenImmersion j.left] (x : Z ⟶ H)
    (hx : ∀ p, x.left p ∈ Set.range j.left) : ∃ y : Z ⟶ U, y ≫ j = x := by
  have hr : Set.range x.left ⊆ Set.range j.left := by rintro _ ⟨p, rfl⟩; exact hx p
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left x.left hr) ?_, Over.OverMorphism.ext
    (IsOpenImmersion.lift_fac j.left x.left hr)⟩
  rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w]
end GlobalTheory.GenericHom
