-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.pMap_pull1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:46.147585+00:00
-- url     : https://prove2.me/submissions/0f00bf65-f962-4809-9a60-07a4ae0dc647

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
    (pMap A S).pull1 x = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (pMap A S) ((boxL (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]
  refine (pjAlg_tmul A S T b 1).trans ?_
  rw [map_one, _root_.mul_one]
  rfl
end GlobalTheory.CompanionTheory.HopfSys
