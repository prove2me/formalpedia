-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.prod_j_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:54.038804+00:00
-- url     : https://prove2.me/submissions/721c4024-3df2-414c-9de4-e9f4d085a539

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.GenProj
theorem _root_.solution (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => (M.prod N).e.inv.left ≫ q) h4).symm.trans h2)
end GlobalTheory.SS.GenProj
