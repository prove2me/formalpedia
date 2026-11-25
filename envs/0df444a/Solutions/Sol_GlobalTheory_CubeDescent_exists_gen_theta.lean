-- Prove2me | solution 1 for GlobalTheory.CubeDescent.exists_gen_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:39.556605+00:00
-- url     : https://prove2.me/submissions/0ca1167d-ae1e-4631-8595-6df7d81dd42d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Theorems.Thm_GlobalTheory_CubeDescent_exists_gen_comp
import Theorems.Thm_GlobalTheory_CubeDescent_exists_gen_descend
import Theorems.Thm_GlobalTheory_CubeDescent_val_eq_of_axis
import Theorems.Thm_GlobalTheory_AbelianQuotient_flat_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_quasiCompact_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_surjective_tensorHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CubeDescent
variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}
variable {A : Over S} [GrpObj A]
variable {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.CubeDescent
theorem _root_.solution [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (ψ : A ⟶ B) [IsMonHom ψ] [Flat ψ.left] [Surjective ψ.left] [QuasiCompact ψ.left]
    {M : LB B.left} (hM : M.IsLB) (t : LB.Gen (Theta A (M.pull ψ.left))) (ht : t.IsGen) :
    ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have := AbelianQuotient.flat_tensorHom ψ ψ
  have := AbelianQuotient.surjective_tensorHom ψ ψ
  have := AbelianQuotient.quasiCompact_tensorHom ψ ψ
  have := AbelianQuotient.flat_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.surjective_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.quasiCompact_tensorHom ψ (ψ ⊗ₘ ψ)
  let π : G3 A ⟶ G3 B := ψ ⊗ₘ ψ ⊗ₘ ψ
  have hπ : ∀ {T : Over S} (x y w : T ⟶ A),
      lift x (lift y w) ≫ π = lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ)) := fun x y w => by
    simp [π, lift_map]
  obtain ⟨u₀, hu₀⟩ := exists_gen_comp M ψ.left (thφ A (x3 A)) thε t ht
  have hφ : ∀ I, thφ A (x3 A) I ≫ ψ.left = π.left ≫ thφ B (x3 B) I := fun I => by
    let ρ : (G3 A ⟶ A) →* (G3 A ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
    exact congrArg (fun q => q.left) ((psum_hom ρ (x3 A) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [ρ, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  obtain ⟨u, hu, -⟩ := exists_gen hM (φ' := fun I => π.left ≫ thφ B (x3 B) I) (ε' := thε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hφ I)) u₀ hu₀
  have hc : ∀ {T : Over S} (x y w : T ⟶ A) (I : thK),
      (lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I =
        (lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ))).left ≫ thφ B (x3 B) I := fun x y w I => by
    rw [← Category.assoc, ← Over.comp_left, hπ]
  have hp : ∀ (x y w : A ⟶ A), (y = 1 ∧ w = 1 ∨ x = 1 ∧ w = 1 ∨ x = 1 ∧ y = 1) →
      ∀ (U : Type) [CommGroup U] (h : (A.left ⟶ B.left) → U),
      ∏ I, h ((lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I) ^ thε I = 1 := by
    intro x y w H U _ h
    refine (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hc x y w I)).trans
      ((prod_cub _ _ _ h).trans ?_)
    apply Additive.ofMul.injective
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [MonObj.one_comp, _root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;>
      abel
  refine exists_gen_descend hM π.left (thφ B (x3 B)) thε u hu fun Z g₁ g₂ z J hJ e => ?_
  let T : Over S := Over.mk (g₂ ≫ (G3 A).hom)
  let k₂ : T ⟶ G3 A := Over.homMk g₂ rfl
  let k₁ : T ⟶ G3 A := Over.homMk g₁ (by
    change g₁ ≫ (G3 A).hom = g₂ ≫ (G3 A).hom
    rw [← Over.w π, reassoc_of% e])
  have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
  obtain ⟨x, y, w, h₁⟩ : ∃ x y w, k₁ = lift x (lift y w) :=
    ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  obtain ⟨x', y', w', h₂⟩ : ∃ x y w, k₂ = lift x (lift y w) :=
    ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  rw [h₁, h₂, hπ, hπ] at e'
  have ex : x ≫ ψ = x' ≫ ψ := by simpa using e' =≫ fst _ _
  have ey : y ≫ ψ = y' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ fst _ _
  have ew : w ≫ ψ = w' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ snd _ _
  change val u k₁.left z J = val u k₂.left z J
  rw [h₁, h₂]
  let σ₁ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _))
  let σ₂ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  have s₁ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₁ = lift b (lift a c) :=
    fun a b c => by simp [σ₁]
  have s₂ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₂ = lift b (lift c a) :=
    fun a b c => by simp [σ₂]
  have v₀ := val_eq_of_axis hG hA hM hu (𝟙 _) (fun U _ h => by
      simp only [Category.comp_id]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).symm) x x'
    (fun T' ρ a b I => by
      rw [Category.comp_id, Category.comp_id]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ex]) (hc _ _ _ I).symm)) y w z J hJ
  have v₁ := val_eq_of_axis hG hA hM hu σ₁ (fun U _ h => by
      simp only [s₁]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inl ⟨rfl, rfl⟩)) U h).symm) y y'
    (fun T' ρ a b I => by
      rw [s₁, s₁]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ey]) (hc _ _ _ I).symm)) x' w z J hJ
  have v₂ := val_eq_of_axis hG hA hM hu σ₂ (fun U _ h => by
      simp only [s₂]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inr ⟨rfl, rfl⟩)) U h).symm) w w'
    (fun T' ρ a b I => by
      rw [s₂, s₂]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ew]) (hc _ _ _ I).symm)) x' y' z J hJ
  rw [Category.comp_id, Category.comp_id] at v₀
  rw [s₁, s₁] at v₁
  rw [s₂, s₂] at v₂
  exact v₀.trans (v₁.trans v₂)
end GlobalTheory.CubeDescent
