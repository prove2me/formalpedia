-- Prove2me | solution 1 for GlobalTheory.translationUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:47.79009+00:00
-- url     : https://prove2.me/submissions/4d5a3910-b232-4feb-bd8e-dfbade7ca9a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TranslationUnitMul
import Theorems.Thm_GlobalTheory_cubN_mul_cubN_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


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
theorem _root_.solution :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e
end GlobalTheory
