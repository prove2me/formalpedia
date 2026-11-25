-- Prove2me | solution 1 for GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:06.301901+00:00
-- url     : https://prove2.me/submissions/6c05a348-a894-43e3-b4b7-4b5b4ffb8bbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrderStatement
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_SS_OrdTwist_main


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
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  first | exact @GlobalTheory.SS.OrdTwist.main | exact GlobalTheory.SS.OrdTwist.main | (intros; apply GlobalTheory.SS.OrdTwist.main <;> assumption)
end _root_.GlobalTheory.T
