-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.rep_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:45.292875+00:00
-- url     : https://prove2.me/submissions/546f5d53-5f1e-4d41-a9f1-59140a53a308

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_comp_idPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (k : ℕ) : Rep D (fun _ x z J => val D.sym (x ^ k).left z J)
    (fun _ _ h => h (𝟙 _ ^ k)⁻¹ * (h (𝟙 _ ^ k))⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L _ _ D.sym (𝟙 D.P.A ^ k).left, pullGen_isGen _ _ _ _ D.sym_gen _,
    fun U _ h => ?_, fun T x z J hJ => ?_⟩
  · rw [Fin.prod_univ_two]
    show h ((𝟙 D.P.A ^ k) ≫ ι[D.P.A]).left ^ (1 : ℤ) * h ((𝟙 D.P.A ^ k).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
    rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl
  · rw [val_pull hJ, ← Over.comp_left, comp_idPow]
end GlobalTheory.UT.PhiOrder
