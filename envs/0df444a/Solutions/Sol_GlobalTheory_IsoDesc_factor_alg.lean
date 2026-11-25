-- Prove2me | solution 1 for GlobalTheory.IsoDesc.factor_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:13.958608+00:00
-- url     : https://prove2.me/submissions/74900968-24cf-4a59-82d8-05e9a615f549

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
namespace GlobalTheory.IsoDesc
theorem _root_.solution {T G U : Type} [CommGroup T] [CommGroup G] [CommGroup U] (e₀ : T →* G) (V : G → U) (A : T → G → U)
    (hA : ∀ t g, V (e₀ t * g) = A t g * V g)
    (h : ∀ t, V (e₀ t) = V (e₀ t)⁻¹ ∧ ∀ y u, V (e₀ t * y) * V (e₀ t * u) * V (y * u) * V 1 =
      V (e₀ t * y * u) * V (e₀ t) * V y * V u) :
    (∀ t t' u, A (t * t') u * (A (t * t') 1)⁻¹ = A t u * (A t 1)⁻¹ * (A t' u * (A t' 1)⁻¹)) ∧
      (∀ t t', A (t * t') 1 = A t (e₀ t') * A t' 1) ∧ ∀ t, A t⁻¹ 1 = A t 1 := by
  have e : ∀ t g, A t g = V (e₀ t * g) * (V g)⁻¹ := fun t g => by rw [hA, mul_inv_cancel_right]
  refine ⟨fun t t' u => ?_, fun t t' => ?_, fun t => ?_⟩
  · have a := congrArg Additive.ofMul ((h t).2 (e₀ t') u)
    apply Additive.ofMul.injective
    simp only [e, map_mul, _root_.mul_one, ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) -a
  · apply Additive.ofMul.injective
    simp only [e, map_mul, _root_.mul_one, ofMul_mul, ofMul_inv]
    abel
  · simp only [e, map_inv, _root_.mul_one, ← (h t).1]
end GlobalTheory.IsoDesc
