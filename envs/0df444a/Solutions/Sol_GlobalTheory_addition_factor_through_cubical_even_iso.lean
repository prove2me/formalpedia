-- Prove2me | solution 1 for GlobalTheory.addition_factor_through_cubical_even_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:13.321854+00:00
-- url     : https://prove2.me/submissions/5aafb3b8-cc84-4dae-8323-d1cfe09f656d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionFactorThroughCubicalEvenIso

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
theorem _root_.solution : ∀ (H U : Type) [CommGroup H] [CommGroup U] (W sL sM : H → U) (cL cM : H → H → H → U) (rL rM : U), rM = W 1 * rL → (∀ x, sM x * W x = W x⁻¹ * sL x) → (∀ x y u, cM x y u * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * cL x y u) → ∀ x y, W x ^ 2 * W y ^ 2 * (cL x y y⁻¹ * (sL y)⁻¹ * rL ^ 2) = cM x y y⁻¹ * (sM y)⁻¹ * rM ^ 2 * (W (x * y) * W (x * y⁻¹)) := by
  intro H U _ _ W sL sM cL cM rL rM hr hs hc x y
  have h1 := hc x y y⁻¹
  rw [mul_inv_cancel, mul_inv_cancel_right] at h1
  have h2 : sM y = W y⁻¹ * sL y * (W y)⁻¹ := eq_mul_inv_of_mul_eq (hs y)
  have h3 : cM x y y⁻¹ = W x * W x * W y * W y⁻¹ * cL x y y⁻¹ *
      (W (x * y) * W (x * y⁻¹) * W 1 * W 1)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [← h1]
    simp only [_root_.mul_assoc]
  rw [h2, h3, hr]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel
end GlobalTheory
