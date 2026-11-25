-- Prove2me | solution 1 for GlobalTheory.PrimCocycle.primitive_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:15:37.403549+00:00
-- url     : https://prove2.me/submissions/4de377ef-1a3e-487d-91df-d686ec4046c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Theorems.Thm_GlobalTheory_PrimCocycle_exists_normalised
import Theorems.Thm_GlobalTheory_PrimCocycle_val_mul_eq

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.PrimCocycle
theorem _root_.solution : GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (O : RigLB B), (∃ t : LB.Gen (abelian₂ B O.L), t.IsGen) → ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen ∧ ∀ (Z : Over S) (z : Z.left) (J : (Z.left ⟶ B.left) → O.L.ι), Geo.Tor.Good O.L z J → let v : (Z ⟶ B) → (Z ⟶ B) → (Z.left.presheaf.stalk z)ˣ := fun x y => Geo.Tor.val (L := O.L) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (ε := fun I => (-1) ^ (2 - I.down.card)) t (lift x y).left z J; (∀ x, v x 1 = 1) ∧ (∀ x y, v x y = v y x) ∧ ∀ x y w, v (x * y) w * v x y = v x (y * w) * v y w := by
  rintro hG S B _ _ hB O ⟨t, ht⟩
  obtain ⟨u, hu, h₀⟩ := exists_normalised O.isLB t ht
  refine ⟨u, hu, fun Z z J hJ => ?_⟩
  show (∀ x, val₂ u z J x 1 = 1) ∧ (∀ x y, val₂ u z J x y = val₂ u z J y x) ∧
    ∀ x y w, val₂ u z J (x * y) w * val₂ u z J x y = val₂ u z J x (y * w) * val₂ u z J y w
  let p₀ := x3 B 0
  let p₁ := x3 B 1
  let p₂ := x3 B 2
  let e : 𝟙_ (Over S) ⟶ G3 B := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o : e ≫ (1 : G3 B ⟶ B) = 1 := MonObj.comp_one _
  have r₀ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₀ = x := fun x y w => by simp [p₀, x3]
  have r₁ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₁ = y := fun x y w => by simp [p₁, x3]
  have r₂ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₂ = w := fun x y w => by simp [p₂, x3]
  refine ⟨fun x => ?_, fun x y => ?_, fun x y w => ?_⟩
  · have := val_mul_eq hG hB O.isLB u hu e p₀ 1 1 1 1 1 1 1 (fun V _ k => by simp) e₀ o o o o o o o
      (lift x (lift x x)) hJ
    rw [r₀, MonObj.comp_one, h₀ Z z J hJ] at this
    simpa using this
  · have := val_mul_eq hG hB O.isLB u hu e p₀ p₁ 1 1 p₁ p₀ 1 1 (fun V _ k => by
      rw [mul_comm p₁ p₀, mul_right_comm (k (p₀ * p₁))]) e₀ e₁ o o e₁ e₀ o o (lift x (lift y x)) hJ
    rw [r₀, r₁] at this
    exact mul_right_cancel this
  · have := val_mul_eq hG hB O.isLB u hu e (p₀ * p₁) p₂ p₀ p₁ p₀ (p₁ * p₂) p₁ p₂ (fun V _ k => by
      rw [_root_.mul_assoc p₀ p₁ p₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])) e₂ e₀ e₁ e₀
      ((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])) e₁ e₂ (lift x (lift y w)) hJ
    rwa [MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂] at this
end GlobalTheory.PrimCocycle
