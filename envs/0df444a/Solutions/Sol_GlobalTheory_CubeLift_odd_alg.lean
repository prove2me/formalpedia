-- Prove2me | solution 1 for GlobalTheory.CubeLift.odd_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:11.759894+00:00
-- url     : https://prove2.me/submissions/f801d582-b275-472f-b58a-498aa2819677

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
theorem _root_.solution {σ s E : B → U} {c c' : U} {x y u : B} (hE : ∀ a, σ a⁻¹ = E a * (s a * σ a))
    (h : σ (x * y * u) * σ x * σ y * σ u = c * σ (x * y) * σ (x * u) * σ (y * u))
    (h' : σ (x⁻¹ * y⁻¹ * u⁻¹) * σ x⁻¹ * σ y⁻¹ * σ u⁻¹ = c' * σ (x⁻¹ * y⁻¹) * σ (x⁻¹ * u⁻¹) * σ (y⁻¹ * u⁻¹))
    (hs : c' * s (x * y) * s (x * u) * s (y * u) = c * s (x * y * u) * s x * s y * s u) :
    E (x * y * u) * E x * E y * E u / E (x * y) / E (x * u) / E (y * u) = 1 := by
  simp only [← mul_inv, hE] at h'
  have a := congrArg Additive.ofMul h
  have b := congrArg Additive.ofMul h'
  have d := congrArg Additive.ofMul hs
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a b d ⊢
  linear_combination (norm := abel) b - a + d
end GlobalTheory.CubeLift
