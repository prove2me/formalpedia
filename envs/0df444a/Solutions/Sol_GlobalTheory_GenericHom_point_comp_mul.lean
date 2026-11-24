-- Prove2me | solution 1 for GlobalTheory.GenericHom.point_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:06.841314+00:00
-- url     : https://prove2.me/submissions/2f7a1706-c30e-4fb5-901a-3d68613df63d

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
theorem _root_.solution {X G : Over (Sp k)} [GrpObj G] (x : 𝟙_ (Over (Sp k)) ⟶ X)
    (a : 𝟙_ (Over (Sp k)) ⟶ G) (g : X ⟶ G) : x ≫ ((toUnit X ≫ a) * g) = a * (x ≫ g) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (𝟙 _), Category.id_comp]
end GlobalTheory.GenericHom
