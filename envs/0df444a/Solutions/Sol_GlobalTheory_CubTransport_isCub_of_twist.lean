-- Prove2me | solution 1 for GlobalTheory.CubTransport.isCub_of_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:06:54.406567+00:00
-- url     : https://prove2.me/submissions/df87c42e-8e19-49f3-a0e4-a87c4ac284b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CubTransport
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.CubTransport
theorem _root_.solution {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (hθ : IsCub θ) (β : A' →* A) (Ω : A' → U) {θ' : A' → A' → A' → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face] at e
    simp only [_root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.s01 (β x) (β y) (β z)
    rw [h, h, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.s12 (β x) (β y) (β z)
    rw [h, h, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h] at e
    simp only [← _root_.mul_assoc x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
end GlobalTheory.CubTransport
