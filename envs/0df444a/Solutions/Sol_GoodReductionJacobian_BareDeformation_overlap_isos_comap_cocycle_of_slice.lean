-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bedba508-60a4-5526-a819-291464f91d03

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices
import Theorems.Thm_GoodReductionJacobian_BareDeformation_eq_of_forall_slice_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_overlap_isos_comap_cocycle_of_slice
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem solution
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (δ : B →+* B') (hδ : (algebraMap B' B₁).comp δ = algebraMap B B₁)
    (p₀ p₁ p₂ : B' →+* B) (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hp₀ : (algebraMap B B₁).comp p₀ = algebraMap B' B₁) (hp₁ : (algebraMap B B₁).comp p₁ = algebraMap B' B₁)
    (hp₂ : (algebraMap B B₁).comp p₂ = algebraMap B' B₁)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (hg' : D₀'.g ≫ h' = D₀.g)
    (k₀ k₁ k₂ : D₀.A ⟶ D₀'.A) (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂))
    (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (hτ'B : ∀ s : 𝒰.Idx 1, (τ' s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτ'g : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ' s).hom = D₀.g ∣_ 𝒰.inter s)
    (hcocτ : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0)
    (hcocτ' : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ' (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0)
    (σ : ∀ s : (𝒰.comap h').Idx 1, ((↑((𝒰.comap h').inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h').inter s)))
    (hσB : (∀ s : (𝒰.comap h').Idx 1, (σ s).hom ≫ ((𝒰.comap h').inter s).ι ≫ D₀'.f = ((𝒰.comap h').inter s).ι ≫ D₀'.f))
    (hσ₀ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₀ → κ ≫ (σ s).hom = κ))
    (hσ₁ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₁ → (τ s).hom ≫ κ = κ ≫ (σ s).hom))
    (hσ₂ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₂ → (τ' s).hom ≫ κ = κ ≫ (σ s).hom)) :
    (∀ r : (𝒰.comap h').Idx 2, ∃ ρ : Fin 3 → ((↑((𝒰.comap h').inter r) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j)
            = D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j) ≫ (σ ((𝒰.comap h').face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) := by
  intro r
  obtain ⟨ρ, hρ, hρc⟩ := hcocτ r
  obtain ⟨ρ', hρ', hρ'c⟩ := hcocτ' r

  have gnat : ∀ j : Fin 3, (D₀.g ∣_ 𝒰.inter r) ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j) =
      A₁.homOfLE (D₀.g.preimage_mono (𝒰.inter_le_inter_face r j)) ≫ (D₀.g ∣_ 𝒰.inter (𝒰.face r j)) := by
    intro j
    rw [← cancel_mono (𝒰.inter (𝒰.face r j)).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

  have overB : ∀ j : Fin 3, ρ j ≫ (𝒰.inter r).ι ≫ D₀.f = (𝒰.inter r).ι ≫ D₀.f := by
    intro j
    rw [← Scheme.homOfLE_ι D₀.A (𝒰.inter_le_inter_face r j)]
    simp only [Category.assoc]
    rw [reassoc_of% (hρ j), hτB]
  have overB' : ∀ j : Fin 3, ρ' j ≫ (𝒰.inter r).ι ≫ D₀.f = (𝒰.inter r).ι ≫ D₀.f := by
    intro j
    rw [← Scheme.homOfLE_ι D₀.A (𝒰.inter_le_inter_face r j)]
    simp only [Category.assoc]
    rw [reassoc_of% (hρ' j), hτ'B]
  have fixg : ∀ j : Fin 3, (D₀.g ∣_ 𝒰.inter r) ≫ ρ j = D₀.g ∣_ 𝒰.inter r := by
    intro j
    rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le_inter_face r j)), Category.assoc, hρ j, ← Category.assoc, gnat j,
      Category.assoc, hτg]
  have fixg' : ∀ j : Fin 3, (D₀.g ∣_ 𝒰.inter r) ≫ ρ' j = D₀.g ∣_ 𝒰.inter r := by
    intro j
    rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le_inter_face r j)), Category.assoc, hρ' j, ← Category.assoc, gnat j,
      Category.assoc, hτ'g]

  have ex := fun j : Fin 3 =>
    GoodReductionJacobian.BareDeformation.exists_endo_comap_inter_of_slices B' B B₁ hπ δ hδ p₀ p₁ p₂ hp₀δ hp₁δ hp₂δ hp₀ hp₁ hp₂ hinj hsurj D₀ D₀' h' hc' hg' k₀ k₁ k₂ hk₀ hk₁ hk₂ hk₀f hk₁f hk₂f 𝒰 r (ρ j) (ρ' j)
      (overB j) (fixg j) (overB' j) (fixg' j)
  choose ρ'' hρ''B hρ''g h0 h1 h2 using ex

  have hle : ∀ (k : D₀.A ⟶ D₀'.A), k ≫ h' = 𝟙 _ → ∀ {n : ℕ} (t : 𝒰.Idx n),
      𝒰.inter t ≤ k ⁻¹ᵁ (𝒰.comap h').inter t := by
    intro k hk n t
    exact le_of_eq (by rw [Scheme.OrderedAffineCover.comap_inter, ← Scheme.Hom.comp_preimage, hk, Scheme.Hom.id_preimage])
  have hκf : ∀ (k : D₀.A ⟶ D₀'.A) (hk : k ≫ h' = 𝟙 _) (j : Fin 3),
      k.resLE ((𝒰.comap h').inter (𝒰.face r j)) (𝒰.inter (𝒰.face r j)) (hle k hk _) ≫
        ((𝒰.comap h').inter (𝒰.face r j)).ι = (𝒰.inter (𝒰.face r j)).ι ≫ k :=
    fun k hk j => Scheme.Hom.resLE_comp_ι _ _
  have hle' : ∀ j : Fin 3, (𝒰.comap h').inter r ≤ (𝒰.comap h').inter (𝒰.face r j) := fun j =>
    (𝒰.comap h').inter_le_inter_face r j
  have nat : ∀ (k : D₀.A ⟶ D₀'.A) (hk : k ≫ h' = 𝟙 _) (j : Fin 3)
      (κ : (↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter r)),
      κ ≫ ((𝒰.comap h').inter r).ι = (𝒰.inter r).ι ≫ k →
      κ ≫ D₀'.A.homOfLE (hle' j) =
        D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫
          k.resLE ((𝒰.comap h').inter (𝒰.face r j)) (𝒰.inter (𝒰.face r j)) (hle k hk _) := by
    intro k hk j κ hκ
    rw [← cancel_mono ((𝒰.comap h').inter (𝒰.face r j)).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, hκ, Scheme.homOfLE_ι_assoc]
  refine ⟨ρ'', fun j => ?_, ?_⟩
  ·
    show ρ'' j ≫ D₀'.A.homOfLE (hle' j) = D₀'.A.homOfLE (hle' j) ≫ (σ (𝒰.face r j)).hom
    apply GoodReductionJacobian.BareDeformation.eq_of_forall_slice_comp_eq B' B B₁ hπ δ hδ p₀ p₁ p₂ hp₀δ hp₁δ hp₂δ hp₀ hp₁ hp₂ hinj hsurj D₀ D₀' h' hc' hg' k₀ k₁ k₂ hk₀ hk₁ hk₂ hk₀f hk₁f hk₂f 𝒰 r (𝒰.face r j)
    · intro κ hκ
      calc κ ≫ ρ'' j ≫ D₀'.A.homOfLE (hle' j)
          = κ ≫ D₀'.A.homOfLE (hle' j) := by rw [← Category.assoc, h0 j κ hκ]
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₀.resLE _ _ (hle k₀ hk₀ _) := nat k₀ hk₀ j κ hκ
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₀.resLE _ _ (hle k₀ hk₀ _) ≫ (σ (𝒰.face r j)).hom := by
            rw [hσ₀ (𝒰.face r j) _ (hκf k₀ hk₀ j)]
        _ = κ ≫ D₀'.A.homOfLE (hle' j) ≫ (σ (𝒰.face r j)).hom := by
            rw [← Category.assoc, ← nat k₀ hk₀ j κ hκ, Category.assoc]
    · intro κ hκ
      calc κ ≫ ρ'' j ≫ D₀'.A.homOfLE (hle' j)
          = ρ j ≫ κ ≫ D₀'.A.homOfLE (hle' j) := by
            rw [← Category.assoc, ← h1 j κ hκ, Category.assoc]
        _ = ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₁.resLE _ _ (hle k₁ hk₁ _) := by rw [nat k₁ hk₁ j κ hκ]
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom ≫ k₁.resLE _ _ (hle k₁ hk₁ _) := by
            rw [← Category.assoc, hρ j, Category.assoc]
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₁.resLE _ _ (hle k₁ hk₁ _) ≫ (σ (𝒰.face r j)).hom := by
            rw [hσ₁ (𝒰.face r j) _ (hκf k₁ hk₁ j)]
        _ = κ ≫ D₀'.A.homOfLE (hle' j) ≫ (σ (𝒰.face r j)).hom := by
            rw [← Category.assoc, ← nat k₁ hk₁ j κ hκ, Category.assoc]
    · intro κ hκ
      calc κ ≫ ρ'' j ≫ D₀'.A.homOfLE (hle' j)
          = ρ' j ≫ κ ≫ D₀'.A.homOfLE (hle' j) := by
            rw [← Category.assoc, ← h2 j κ hκ, Category.assoc]
        _ = ρ' j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₂.resLE _ _ (hle k₂ hk₂ _) := by rw [nat k₂ hk₂ j κ hκ]
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ' (𝒰.face r j)).hom ≫ k₂.resLE _ _ (hle k₂ hk₂ _) := by
            rw [← Category.assoc, hρ' j, Category.assoc]
        _ = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ k₂.resLE _ _ (hle k₂ hk₂ _) ≫ (σ (𝒰.face r j)).hom := by
            rw [hσ₂ (𝒰.face r j) _ (hκf k₂ hk₂ j)]
        _ = κ ≫ D₀'.A.homOfLE (hle' j) ≫ (σ (𝒰.face r j)).hom := by
            rw [← Category.assoc, ← nat k₂ hk₂ j κ hκ, Category.assoc]
  ·
    apply GoodReductionJacobian.BareDeformation.eq_of_forall_slice_comp_eq B' B B₁ hπ δ hδ p₀ p₁ p₂ hp₀δ hp₁δ hp₂δ hp₀ hp₁ hp₂ hinj hsurj D₀ D₀' h' hc' hg' k₀ k₁ k₂ hk₀ hk₁ hk₂ hk₀f hk₁f hk₂f 𝒰 r r
    · intro κ hκ
      rw [h0 1 κ hκ, ← Category.assoc, h0 2 κ hκ, h0 0 κ hκ]
    · intro κ hκ
      rw [← h1 1 κ hκ, hρc, Category.assoc, h1 0 κ hκ, ← Category.assoc, h1 2 κ hκ, Category.assoc]
    · intro κ hκ
      rw [← h2 1 κ hκ, hρ'c, Category.assoc, h2 0 κ hκ, ← Category.assoc, h2 2 κ hκ, Category.assoc]

end S_GoodReductionJacobian_BareDeformation_overlap_isos_comap_cocycle_of_slice
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_overlap_isos_comap_cocycle_of_slice (solution)
