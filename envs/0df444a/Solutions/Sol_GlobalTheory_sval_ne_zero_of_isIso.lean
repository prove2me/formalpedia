-- Prove2me | solution 1 for GlobalTheory.sval_ne_zero_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:04.586696+00:00
-- url     : https://prove2.me/submissions/8f0bd15c-c89c-42a8-a491-e536899c9109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsNeZeroIffSvalGenericPointNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Theorems.Thm_GlobalTheory_gs_eq_stalkMap_gs_id
import Theorems.Thm_GlobalTheory_exists_ne_zero_iff_sval_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)), (∃ j, s.f j ≠ 0) → ∀ (Y' : Scheme.{0}) (τ : Y' ⟶ Y) [IsIso τ] (y : Y') (J), Good L y J → sval s τ y J ≠ 0 := by
  intro X Y _ L hL K _ φ ε s hs Y' τ _ y J hJ h0
  have hG : Good L (τ y) (fun χ : Y ⟶ X => J (τ ≫ χ)) := fun χ => hJ (τ ≫ χ)
  have h1 := (exists_ne_zero_iff_sval_ne_zero s hG).1 hs
  rw [sval_of s (𝟙 Y) (τ y) _ (fun k => J (τ ≫ φ k)) (fun k => by rw [Category.id_comp])] at h1
  apply h1
  have h2 : gs τ y (LB.wchart L φ (fun k => J (τ ≫ φ k))) (s.f (fun k => J (τ ≫ φ k))) = 0 := h0
  have h3 := (gs_eq_stalkMap_gs_id τ y _ (hJ.mem φ τ) _).symm.trans h2
  have hinj : Function.Injective (τ.stalkMap y).hom :=
    (ConcreteCategory.bijective_of_isIso (τ.stalkMap y)).1
  exact (map_eq_zero_iff _ hinj).1 h3
end GlobalTheory
