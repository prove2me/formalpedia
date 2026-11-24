-- Prove2me | solution 1 for GlobalTheory.quotient_descend_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:46.272835+00:00
-- url     : https://prove2.me/submissions/0717eed8-0c18-4cdd-89fb-747bed18b8ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
import Theorems.Thm_GlobalTheory_QuotientDescent_up_left
import Theorems.Thm_GlobalTheory_QuotientDescent_hom_ext
import Theorems.Thm_GlobalTheory_QuotientDescent_up_comp
import Theorems.Thm_GlobalTheory_QuotientDescent_up_injective
import Theorems.Thm_GlobalTheory_QuotientDescent_Equivariant_exists_up
import Theorems.Thm_GlobalTheory_QuotientDescent_equivariant_up
import Theorems.Thm_GlobalTheory_QuotientDescent_mem_equivariantSubgroup

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open QuotientDescent
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).hom (τ g).hom ∧ ∀ c, (a.act c).left ≫ (τ g).hom = (τ g).hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by
  intro Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ
  have hq : IsAffineQuotient ρ π :=
    ⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩
  have hp (g) := (hτ g).2.1
  have f₀ : Flat (𝟙_ (Over X')).hom := inferInstanceAs (Flat (𝟙 X'))
  have f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom :=
    inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))
  have inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y :=
    up_injective hq H hT e
  have ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G}
      (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w :=
    ((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT
  have mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T :=
    (mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)
  obtain ⟨m, hm⟩ := ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := ex f₀ (one_mem _)
  obtain ⟨i, hi⟩ := ex hG' (inv_mem (mem (𝟙 G')))
  have hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c :=
    ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by
      rw [Over.comp_left, Category.assoc, (hτ g).2.2,
        reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])
  choose b hb using hb
  have hm' {T : Over X'} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  have hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c := by
    rw [up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (f₂ f₀ hG') (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (f₂ hG' f₀) (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have : IsCommMonObj G' := ⟨inj (f₂ hG' hG') (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  let a' : OAct O G' :=
    { act := b
      hom c := by
        have := a.hom c
        refine ⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩
        · rw [hb']
          change up H e ≫ _ = up H e
          rw [he, MonObj.one_comp]
        · rw [hb']
          change up H m ≫ _ = up H (_ ≫ m)
          rw [hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]
      one := inj hG' (by rw [hb, a.one, Category.comp_id])
      mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])
      add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨s, hs⟩ := sec (T := T)
    have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
      QuotientDescent.hom_ext H ((k y₀).trans hy)]
  · obtain ⟨s, hs⟩ := sec (T := G)
    have k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    let u : Over.mk (G.hom ≫ π) ⟶ G' := Over.homMk φ H.w
    have hu : s ≫ up H u = 𝟙 G := QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)
    have := k (u ≫ b c)
    rwa [hb', reassoc_of% hu] at this
end GlobalTheory
