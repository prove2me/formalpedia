-- Prove2me | solution 1 for GlobalTheory.T.generic_isomorphism_product_models
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:11:04.091893+00:00
-- url     : https://prove2.me/submissions/7bdeda62-8490-47eb-804d-ae72780d2555

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModelsStatement
import Theorems.Thm_GlobalTheory_SS_GenProj_genIso_of_prod


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
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  first | exact @GlobalTheory.SS.GenProj.genIso_of_prod | exact GlobalTheory.SS.GenProj.genIso_of_prod | (intros; apply GlobalTheory.SS.GenProj.genIso_of_prod <;> assumption)
end _root_.GlobalTheory.T
