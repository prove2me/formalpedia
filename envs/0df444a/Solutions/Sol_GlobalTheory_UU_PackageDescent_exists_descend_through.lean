-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_descend_through
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:41:08.49722+00:00
-- url     : https://prove2.me/submissions/1ca72b66-def2-4197-a3f7-d7ee05632cec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_GlobalTheory_UU_PackageDescent_exists_gen_descend_val
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {X X' Y Y' Z : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π]
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → g₁ ≫ π = g₂ ≫ π →
      (∏ k, gw w (g₁ ≫ φ' k) z (I ((g₁ ≫ φ' k) ≫ F)) (J (g₁ ≫ φ' k)) ^ ε k) * val a g₁ z J =
      (∏ k, gw w (g₂ ≫ φ' k) z (I ((g₂ ≫ φ' k) ≫ F)) (J (g₂ ≫ φ' k)) ^ ε k) * val a g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val t (r ≫ π) z I =
        (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val hM π φ ε u hu fun Z g₁ g₂ z I hI e => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    rw [key Z g₁ z I J hI hJ, key Z g₂ z I J hI hJ, h Z g₁ g₂ z I J hI hJ e]
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩
end GlobalTheory.UU.PackageDescent
