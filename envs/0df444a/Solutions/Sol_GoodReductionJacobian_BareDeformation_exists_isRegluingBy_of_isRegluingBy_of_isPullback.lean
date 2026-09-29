-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3d3d302b-ad17-5915-b45f-e3693501f6b8

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

namespace P2mWs2RBC

theorem slice_isPullback {X X' S S' : Scheme.{0}} (k : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (b : S ⟶ S')
    (hkc : IsPullback k f f' b) (W : X.Opens) (W' : X'.Opens) (hW : k ⁻¹ᵁ W' = W)
    (r : (↑W : Scheme.{0}) ⟶ ↑W') (hr : r ≫ W'.ι = W.ι ≫ k) :
    IsPullback r (W.ι ≫ f) (W'.ι ≫ f') b :=
  (IsOpenImmersion.isPullback r W.ι W'.ι k hr.symm (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hW])).paste_vert hkc

theorem range_subset {X X' : Scheme.{0}} (k : X ⟶ X') (h₀ : X' ⟶ X) (hk : k ≫ h₀ = 𝟙 X) (W : X.Opens) :
    Set.range (W.ι ≫ k).base ⊆ Set.range (h₀ ⁻¹ᵁ W).ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  show h₀.base (k.base (W.ι.base x)) ∈ (W : Set X)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk, Category.comp_id]
  exact x.2

theorem preimage_preimage_eq {X X' : Scheme.{0}} (k : X ⟶ X') (h₀ : X' ⟶ X) (hk : k ≫ h₀ = 𝟙 X) (W : X.Opens) :
    k ⁻¹ᵁ (h₀ ⁻¹ᵁ W) = W := by
  rw [← Scheme.Hom.comp_preimage, hk]; rfl

end P2mWs2RBC

open P2mWs2RBC in
theorem solution
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (h₀ : D₀'.A ⟶ D₀.A) [IsAffineHom h₀]
    (k : D₀.A ⟶ D₀'.A) (hk : k ≫ h₀ = 𝟙 D₀.A)
    (hkc : IsPullback k D₀.f D₀'.f (Spec.map (CommRingCat.ofHom φ))) (hkg : D₀.g ≫ k = D₀'.g)
    (𝒰 : D₀.A.OrderedAffineCover)
    (r : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h₀).inter s)))
    (hr : ∀ s : 𝒰.Idx 1, r s ≫ ((𝒰.comap h₀).inter s).ι = (𝒰.inter s).ι ≫ k)
    (σ : ∀ s : (𝒰.comap h₀).Idx 1, ((↑((𝒰.comap h₀).inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h₀).inter s)))
    (P : BareDeformation f₁ L₁ B') (hP : D₀'.IsRegluingBy (𝒰.comap h₀) σ P)
    (Dφ : BareDeformation f₁ L₁ B) (h : Dφ.A ⟶ P.A)
    (hc : IsPullback h Dφ.f P.f (Spec.map (CommRingCat.ofHom φ))) (hg : Dφ.g ≫ h = P.g) :
    ∃ τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      D₀.IsRegluingBy 𝒰 τ Dφ ∧ ∀ s : 𝒰.Idx 1, (τ s).hom ≫ r s = r s ≫ (σ s).hom := by
  obtain ⟨hσB, hσg, ι', hι'open, hι'B, hι'surj, hι'g, hι'glue⟩ := hP
  have hkf : k ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom φ) := hkc.w

  have hslice : ∀ s : 𝒰.Idx 1, IsPullback (r s) ((𝒰.inter s).ι ≫ D₀.f) (((𝒰.comap h₀).inter s).ι ≫ D₀'.f)
      (Spec.map (CommRingCat.ofHom φ)) := fun s =>
    slice_isPullback k D₀.f D₀'.f _ hkc _ _ (by rw [Scheme.OrderedAffineCover.comap_inter, preimage_preimage_eq k h₀ hk]) (r s) (hr s)

  have hτc : ∀ s : 𝒰.Idx 1, (r s ≫ (σ s).hom) ≫ ((𝒰.comap h₀).inter s).ι ≫ D₀'.f =
      ((𝒰.inter s).ι ≫ D₀.f) ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro s; rw [Category.assoc, hσB, ← Category.assoc, hr, Category.assoc, hkf, Category.assoc]
  have hτc' : ∀ s : 𝒰.Idx 1, (r s ≫ (σ s).inv) ≫ ((𝒰.comap h₀).inter s).ι ≫ D₀'.f =
      ((𝒰.inter s).ι ≫ D₀.f) ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro s
    rw [Category.assoc, (σ s).inv_comp_eq.mpr (hσB s).symm, ← Category.assoc, hr, Category.assoc, hkf, Category.assoc]
  let τh : ∀ s : 𝒰.Idx 1, (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s) := fun s => (hslice s).lift _ _ (hτc s)
  let τi : ∀ s : 𝒰.Idx 1, (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s) := fun s => (hslice s).lift _ _ (hτc' s)
  have hτr : ∀ s, τh s ≫ r s = r s ≫ (σ s).hom := fun s => (hslice s).lift_fst _ _ _
  have hτB : ∀ s, τh s ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f := fun s => (hslice s).lift_snd _ _ _
  have hτir : ∀ s, τi s ≫ r s = r s ≫ (σ s).inv := fun s => (hslice s).lift_fst _ _ _
  have hτiB : ∀ s, τi s ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f := fun s => (hslice s).lift_snd _ _ _
  have h1 : ∀ s, τh s ≫ τi s = 𝟙 _ := fun s => by
    apply (hslice s).hom_ext
    · rw [Category.assoc, hτir, ← Category.assoc, hτr, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hτiB, hτB, Category.id_comp]
  have h2 : ∀ s, τi s ≫ τh s = 𝟙 _ := fun s => by
    apply (hslice s).hom_ext
    · rw [Category.assoc, hτr, ← Category.assoc, hτir, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hτB, hτiB, Category.id_comp]
  let τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)) := fun s => ⟨τh s, τi s, h1 s, h2 s⟩

  let kU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ ↑((𝒰.comap h₀).U i) := fun i =>
    IsOpenImmersion.lift ((𝒰.comap h₀).U i).ι ((𝒰.U i).ι ≫ k) (range_subset k h₀ hk (𝒰.U i))
  have hkU : ∀ i, kU i ≫ ((𝒰.comap h₀).U i).ι = (𝒰.U i).ι ≫ k := fun i => IsOpenImmersion.lift_fac _ _ _
  have hsliceU : ∀ i : 𝒰.ι, IsPullback (kU i) ((𝒰.U i).ι ≫ D₀.f) (((𝒰.comap h₀).U i).ι ≫ D₀'.f)
      (Spec.map (CommRingCat.ofHom φ)) := fun i =>
    slice_isPullback k D₀.f D₀'.f _ hkc _ _ (preimage_preimage_eq k h₀ hk (𝒰.U i)) (kU i) (hkU i)

  have hcc : ∀ i, (kU i ≫ ι' i) ≫ P.f = ((𝒰.U i).ι ≫ D₀.f) ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro i; rw [Category.assoc, hι'B, ← Category.assoc, hkU, Category.assoc, hkf, Category.assoc]
  let ιφ : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ Dφ.A := fun i => hc.lift _ _ (hcc i)
  have hιφh : ∀ i, ιφ i ≫ h = kU i ≫ ι' i := fun i => hc.lift_fst _ _ _
  have hιφB : ∀ i, ιφ i ≫ Dφ.f = (𝒰.U i).ι ≫ D₀.f := fun i => hc.lift_snd _ _ _

  have hsq : ∀ i, IsPullback (kU i) (ιφ i) (ι' i) h := by
    intro i
    refine IsPullback.of_bot ?_ (hιφh i).symm hc
    rw [hιφB, hι'B]
    exact hsliceU i
  refine ⟨τ, ⟨hτB, ?_, ιφ, ?_, hιφB, ?_, ?_, ?_⟩, hτr⟩
  ·
    intro s
    apply (hslice s).hom_ext
    · show ((D₀.g ∣_ 𝒰.inter s) ≫ τh s) ≫ r s = (D₀.g ∣_ 𝒰.inter s) ≫ r s

      have hle : D₀.g ⁻¹ᵁ 𝒰.inter s ≤ D₀'.g ⁻¹ᵁ (𝒰.comap h₀).inter s := by
        rw [Scheme.OrderedAffineCover.comap_inter, ← hkg, Scheme.Hom.comp_preimage, preimage_preimage_eq k h₀ hk]
      have hfac : (D₀.g ∣_ 𝒰.inter s) ≫ r s = A₁.homOfLE hle ≫ (D₀'.g ∣_ (𝒰.comap h₀).inter s) := by
        rw [← cancel_mono ((𝒰.comap h₀).inter s).ι, Category.assoc, hr, ← Category.assoc, morphismRestrict_ι,
          Category.assoc, hkg, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
      rw [Category.assoc, hτr, ← Category.assoc, hfac, Category.assoc, hσg]
    · rw [Category.assoc, hτB]
  ·
    intro i
    haveI := hι'open i
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hsq i) (hι'open i)
  ·
    intro x
    obtain ⟨i, y', hy'⟩ := hι'surj (h.base x)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι' i) (g := h) y' x hy'
    refine ⟨i, (hsq i).isoPullback.inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, (hsq i).isoPullback_inv_snd]
    exact hz2
  ·
    intro i
    apply hc.hom_ext
    · have hle : D₀.g ⁻¹ᵁ 𝒰.U i ≤ D₀'.g ⁻¹ᵁ (𝒰.comap h₀).U i := by
        rw [Scheme.OrderedAffineCover.comap_U, ← hkg, Scheme.Hom.comp_preimage, preimage_preimage_eq k h₀ hk]
      have hfac : (D₀.g ∣_ 𝒰.U i) ≫ kU i = A₁.homOfLE hle ≫ (D₀'.g ∣_ (𝒰.comap h₀).U i) := by
        rw [← cancel_mono ((𝒰.comap h₀).U i).ι, Category.assoc, hkU, ← Category.assoc, morphismRestrict_ι,
          Category.assoc, hkg, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
      rw [Category.assoc, hιφh, ← Category.assoc, hfac, Category.assoc, hι'g, Scheme.homOfLE_ι_assoc, Category.assoc, hg]
    · rw [Category.assoc, hιφB, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, Dφ.cart.w, D₀.cart.w]
  ·
    intro s
    apply hc.hom_ext
    ·
      have hk0 : D₀.A.homOfLE (𝒰.inter_le s 0) ≫ kU (s.1 0) = r s ≫ D₀'.A.homOfLE ((𝒰.comap h₀).inter_le s 0) := by
        rw [← cancel_mono ((𝒰.comap h₀).U (s.1 0)).ι, Category.assoc, hkU, Scheme.homOfLE_ι_assoc, Category.assoc,
          Scheme.homOfLE_ι, hr]
      have hk1 : D₀.A.homOfLE (𝒰.inter_le s 1) ≫ kU (s.1 1) = r s ≫ D₀'.A.homOfLE ((𝒰.comap h₀).inter_le s 1) := by
        rw [← cancel_mono ((𝒰.comap h₀).U (s.1 1)).ι, Category.assoc, hkU, Scheme.homOfLE_ι_assoc, Category.assoc,
          Scheme.homOfLE_ι, hr]
      rw [Category.assoc, hιφh, ← Category.assoc, hk0, Category.assoc, hι'glue, Category.assoc, Category.assoc, hιφh,
        ← Category.assoc (D₀.A.homOfLE _), hk1]
      show r s ≫ (σ s).hom ≫ _ = τh s ≫ (r s ≫ _) ≫ _
      rw [Category.assoc, ← Category.assoc (τh s), hτr, Category.assoc]
    · rw [Category.assoc, hιφB, Scheme.homOfLE_ι_assoc, Category.assoc, Category.assoc, hιφB, Scheme.homOfLE_ι_assoc]
      exact (hτB s).symm

end S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback (solution)
