-- Prove2me | solution 1 for GlobalTheory.T.exists_torusStableGoodOpen_of_weightUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:25.12427+00:00
-- url     : https://prove2.me/submissions/562509d0-12b1-4c1d-bc67-85cd789a6a7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Theorems.Thm_GlobalTheory_SS_exists_goodOpen_of_weight_units


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ χ : X, ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ) → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) := by
  first | exact @GlobalTheory.SS.exists_goodOpen_of_weight_units | exact GlobalTheory.SS.exists_goodOpen_of_weight_units | (intros; apply GlobalTheory.SS.exists_goodOpen_of_weight_units <;> assumption)
end _root_.GlobalTheory.T
