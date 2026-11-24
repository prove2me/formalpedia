-- Prove2me | solution 1 for GlobalTheory.DegPull.isCub_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:47.988113+00:00
-- url     : https://prove2.me/submissions/af91a1a8-3708-4247-8e62-6c6af05e5e31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
namespace GlobalTheory.DegPull
theorem _root_.solution {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} (hθ : IsCub θ)
    (β : A →* B) (Ω : A → U) (θ' : A → A → A → U)
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face, _root_.one_mul, _root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := h x y z
    rw [hθ.s01, h y x z, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := h x y z
    rw [hθ.s12, h x z y, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h, ← _root_.mul_assoc x x' x''] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
end GlobalTheory.DegPull
