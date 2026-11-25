-- Prove2me | solution 1 for GlobalTheory.LocTriv.hom_ext_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:57.615738+00:00
-- url     : https://prove2.me/submissions/2226395a-5912-4055-9e2b-121ac4565bc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_UU_IsWt_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
namespace GlobalTheory.LocTriv
theorem _root_.solution {Z Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {a b : Z ⟶ Y}
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b :=  by
  haveI : IsAffine U.toScheme := hU
  have h1 : a.resLE U ⊤ ha = b.resLE U ⊤ hb := by
    apply ext_of_isAffine
    show (a.resLE U ⊤ ha).app ⊤ = (b.resLE U ⊤ hb).app ⊤
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, h]
  have h2 := congrArg (· ≫ U.ι) h1
  simp only [Scheme.Hom.resLE_comp_ι] at h2
  calc a = Z.topIso.inv ≫ (⊤ : Z.Opens).ι ≫ a := by
        rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
    _ = Z.topIso.inv ≫ (⊤ : Z.Opens).ι ≫ b := by rw [h2]
    _ = b := by rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
end GlobalTheory.LocTriv
