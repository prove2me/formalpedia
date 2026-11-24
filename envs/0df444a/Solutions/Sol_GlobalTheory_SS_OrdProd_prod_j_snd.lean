-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.prod_j_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:14.431504+00:00
-- url     : https://prove2.me/submissions/a9c0516e-470a-45da-8f1e-08eb839192b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h1 := congrArg (fun f => f.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h2 : ((Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y)).left ≫
      pullback.fst N.Y.hom (spMap (algebraMap R K)) =
      pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (snd M.Y N.Y).left := pullback.lift_fst _ _ _
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)).trans
    ((Category.assoc _ _ _).symm.trans (h1.trans (Category.assoc _ _ _)))
end GlobalTheory.SS.OrdProd
