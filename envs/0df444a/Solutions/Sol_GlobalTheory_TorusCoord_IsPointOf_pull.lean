-- Prove2me | solution 1 for GlobalTheory.TorusCoord.IsPointOf.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:38.7547+00:00
-- url     : https://prove2.me/submissions/720878ea-726b-433c-967d-d8088abbbe90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusCoord
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.TorusCoord
namespace IsPointOf
theorem _root_.solution {T T' : Over (Spec (CommRingCat.of R))} {x : T.left ⟶ (thickObj R I e G).left}
    {ξ : GtPt D T} {ξ' : GtPt D T'} (h : IsPointOf g x ξ) {f : T'.left ⟶ T.left} (hf : GtPt.IsPull f ξ ξ') :
    IsPointOf g (f ≫ x) ξ' :=
  ⟨by rw [hf.1, h.1, Category.assoc], fun χ => DVR.corr_trans D.P.isLB (hf.2 χ)
    (DVR.corr_trans D.P.isLB (DVR.corr_pullGen (h.2 χ) f) (DVR.corr_pullGen_comp _ _ _))⟩
end IsPointOf
end GlobalTheory.TorusCoord
