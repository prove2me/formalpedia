-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.qMap_pull1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:59.00792+00:00
-- url     : https://prove2.me/submissions/9f19bc62-c3fd-43e7-aaef-32799ef81cb0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (x : H1 (OSys A.hom S)) :
    (qMap A S).pull1 x = (pj A S).coef.pull1 ((boxR (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (qMap A S) ((boxR (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]
  refine (pjAlg_tmul A S T 1 b).trans ?_
  rw [map_one, _root_.one_mul]
  rfl
end GlobalTheory.CompanionTheory.HopfSys
