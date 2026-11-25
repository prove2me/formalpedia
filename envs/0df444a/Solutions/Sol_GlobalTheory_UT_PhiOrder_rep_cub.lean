-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.rep_cub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:40.276821+00:00
-- url     : https://prove2.me/submissions/f781a355-f9fb-4930-bc12-176e7095d367

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


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
theorem _root_.solution (k : ℕ) : Rep D (fun _ x z J => th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k))
    (fun _ _ h => h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k) * (h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹))⁻¹ * (h (𝟙 _ ^ k * 𝟙 _ ^ k))⁻¹ *
      (h ((𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k))⁻¹ * h (𝟙 _ ^ k) * h (𝟙 _ ^ k)⁻¹ * h (𝟙 _ ^ k) * (h 1)⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (𝟙 D.P.A ^ k) (lift (𝟙 D.P.A ^ k)⁻¹ (𝟙 D.P.A ^ k))).left, pullGen_isGen _ _ _ _ D.cub.isGen _,
    fun U _ h => prod_cub _ _ _ h, fun T x z J hJ => ?_⟩
  rw [val_cub D.cub x hJ, show x ≫ (𝟙 D.P.A ^ k)⁻¹ = (x ≫ (𝟙 D.P.A ^ k))⁻¹ from map_inv (preHom x) _, comp_idPow]
end GlobalTheory.UT.PhiOrder
