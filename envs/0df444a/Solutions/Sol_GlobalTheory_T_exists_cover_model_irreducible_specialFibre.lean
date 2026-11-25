-- Prove2me | solution 1 for GlobalTheory.T.exists_cover_model_irreducible_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:38.751902+00:00
-- url     : https://prove2.me/submissions/0735f246-36c3-4eea-905a-28f0de71b097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Theorems.Thm_GlobalTheory_SS_IrrSplit_exists_cover_irr


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
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  first | exact @GlobalTheory.SS.IrrSplit.exists_cover_irr | exact GlobalTheory.SS.IrrSplit.exists_cover_irr | (intros; apply GlobalTheory.SS.IrrSplit.exists_cover_irr <;> assumption)
end _root_.GlobalTheory.T
