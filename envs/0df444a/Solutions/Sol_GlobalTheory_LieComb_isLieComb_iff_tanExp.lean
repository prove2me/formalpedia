-- Prove2me | solution 1 for GlobalTheory.LieComb.isLieComb_iff_tanExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:59.136657+00:00
-- url     : https://prove2.me/submissions/2ac5c797-8241-4054-9b3f-68a168f68f28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Theorems.Thm_GlobalTheory_SqZero_isLieComb_iff_lieExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieComb
open GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}
namespace GlobalTheory.LieComb
theorem _root_.solution (c : Fin n → R) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = tanExp v c := isLieComb_iff_lieExp c w
end GlobalTheory.LieComb
