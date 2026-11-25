-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.kMap_mMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:22.51703+00:00
-- url     : https://prove2.me/submissions/e67c66f1-17da-4bd8-b3d0-f5fe0bb53810

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_appLE_chain
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_appLE_id

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
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
attribute [local instance] unit_isAffine
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (y : (OSys A.hom S).obj b) :
    (kMap ha).α b ((mMap A S).α ((tK a₀).obj b) y) = y :=
  (appLE_chain (iota A).left μ[A].left (𝟙 _) (iota_mul A) _ _ le_rfl y).trans (appLE_id _ _ y)
end GlobalTheory.CompanionTheory.HopfSys
