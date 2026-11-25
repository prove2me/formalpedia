-- Prove2me | solution 1 for GlobalTheory.CubeLift.cub_red_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:28:33.70003+00:00
-- url     : https://prove2.me/submissions/f0409399-eec7-42af-b354-70ac615996b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {B C U : Type} [CommGroup B] [CommGroup C] [CommGroup U]
namespace GlobalTheory.CubeLift
theorem _root_.solution {a₁ a₂ a₃ a₄ a₅ a₆ a₇ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₀ c c₀ D v₁ v₂ v₃ v₄ v₅ v₆ v₇ : U}
    (h₀ : a₁ * a₂ * a₃ * a₄ = c₀ * a₅ * a₆ * a₇) (hc : c * w₅ * w₆ * w₇ * w₀ = w₁ * w₂ * w₃ * w₄ * c₀)
    (r₁ : v₁ = w₁ * w₀⁻¹ * a₁) (r₂ : v₂ = w₂ * w₀⁻¹ * a₂) (r₃ : v₃ = w₃ * w₀⁻¹ * a₃) (r₄ : v₄ = w₄ * w₀⁻¹ * a₄)
    (r₅ : v₅ = w₅ * w₀⁻¹ * a₅) (r₆ : v₆ = w₆ * w₀⁻¹ * a₆) (r₇ : v₇ = w₇ * w₀⁻¹ * a₇)
    (h : v₁ * v₂ * v₃ * v₄ = D * (c * v₅ * v₆ * v₇)) : D = 1 := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul h₀
  have b := congrArg Additive.ofMul hc
  have d := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a b d ⊢
  linear_combination (norm := abel) a - b - d
end GlobalTheory.CubeLift
