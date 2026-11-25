-- Prove2me | solution 1 for GlobalTheory.T.exists_lift_oneParameter_quotient_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:19.894422+00:00
-- url     : https://prove2.me/submissions/b677da5f-3b21-4f1d-a66e-ce103da772cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorusStatement
import Theorems.Thm_GlobalTheory_SS_exists_lift_oneParameter


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → ∃ j : Gm (Sp k) ⟶ G, IsMonHom j ∧ j ≫ q = f := by
  first | exact @GlobalTheory.SS.exists_lift_oneParameter | exact GlobalTheory.SS.exists_lift_oneParameter | (intros; apply GlobalTheory.SS.exists_lift_oneParameter <;> assumption)
end _root_.GlobalTheory.T
