-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.isPullO_over_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:40.960547+00:00
-- url     : https://prove2.me/submissions/37b099ee-fbef-40e9-9a32-5a93a0a3502d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans


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
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (Y : Over (Sp R)) (c : HO1 Y.hom) : IsPullO (wOver (𝟙 Y)) c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull (wOver (𝟙 Y))) (pairRes _ Y.hom) (pairIdTrans Y.left) (fun _ _ ↦ rfl) c
end GlobalTheory.CompanionTheory.HopfSys
