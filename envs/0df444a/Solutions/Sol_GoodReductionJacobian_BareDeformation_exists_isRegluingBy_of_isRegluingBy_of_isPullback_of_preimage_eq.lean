-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/209b7877-ec95-5c2e-a1a4-64e52949b5bf

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 4000000 in
theorem solution
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (φ : B →+* B)
    (k₀ : D₀.A ⟶ D₀.A) (hk₀ : IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g) (hk₀U : ∀ a : 𝒰.ι, k₀ ⁻¹ᵁ 𝒰.U a = 𝒰.U a)
    (Dφ : BareDeformation fₛ Lₛ B) (h : Dφ.A ⟶ D.A)
    (hh : IsPullback h Dφ.f D.f (Spec.map (CommRingCat.ofHom φ))) (hhg : Dφ.g ≫ h = D.g)
    (hle : ∀ s : 𝒰.Idx 1, 𝒰.inter s ≤ k₀ ⁻¹ᵁ 𝒰.inter s) :
    ∃ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      (∀ s : 𝒰.Idx 1, (τ' s).hom ≫ k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) =
        k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) ≫ (τ s).hom) ∧
      D₀.IsRegluingBy 𝒰 τ' Dφ := by
  obtain ⟨hτf, hτg, ι, hιo, hιf, hsurj, hιg, hglue⟩ := hD

  have cartW' : ∀ (W : D₀.A.Opens) (heq : k₀ ⁻¹ᵁ W = W) (hW : W ≤ k₀ ⁻¹ᵁ W),
      IsPullback (k₀.resLE W W hW) (W.ι ≫ D₀.f) (W.ι ≫ D₀.f) (Spec.map (CommRingCat.ofHom φ)) := by
    intro W heq hW
    have big : IsPullback (k₀ ∣_ W) ((k₀ ⁻¹ᵁ W).ι ≫ D₀.f) (W.ι ≫ D₀.f) (Spec.map (CommRingCat.ofHom φ)) :=
      (isPullback_morphismRestrict k₀ W).paste_vert hk₀
    haveI : IsIso (D₀.A.homOfLE hW) := by
      rw [← Scheme.isoOfEq_hom D₀.A heq.symm]; infer_instance
    have sq0 : IsPullback (D₀.A.homOfLE hW) (W.ι ≫ D₀.f) ((k₀ ⁻¹ᵁ W).ι ≫ D₀.f) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, Scheme.homOfLE_ι]⟩
    have := sq0.paste_horiz big
    rw [Category.id_comp] at this
    exact this

  have heqI : ∀ s : 𝒰.Idx 1, k₀ ⁻¹ᵁ 𝒰.inter s = 𝒰.inter s := by
    intro s
    show k₀ ⁻¹ᵁ (⨅ j, 𝒰.U (s.1 j)) = ⨅ j, 𝒰.U (s.1 j)
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    exact iInf_congr fun j => hk₀U (s.1 j)
  have hleU : ∀ i : 𝒰.ι, 𝒰.U i ≤ k₀ ⁻¹ᵁ 𝒰.U i := fun i => (hk₀U i).symm ▸ le_rfl
  have cartW : ∀ (W : D₀.A.Opens) (hW : W ≤ k₀ ⁻¹ᵁ W), (k₀ ⁻¹ᵁ W = W) →
      IsPullback (k₀.resLE W W hW) (W.ι ≫ D₀.f) (W.ι ≫ D₀.f) (Spec.map (CommRingCat.ofHom φ)) :=
    fun W hW heq => cartW' W heq hW

  have τ'ex : ∀ s : 𝒰.Idx 1, ∃ τ' : ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      τ'.hom ≫ k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) = k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) ≫ (τ s).hom ∧
      τ'.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f := by
    intro s
    have P := cartW (𝒰.inter s) (hle s) (heqI s)
    refine ⟨⟨P.lift (k₀.resLE _ _ (hle s) ≫ (τ s).hom) ((𝒰.inter s).ι ≫ D₀.f) (by rw [Category.assoc, hτf, P.w]),
      P.lift (k₀.resLE _ _ (hle s) ≫ (τ s).inv) ((𝒰.inter s).ι ≫ D₀.f) (by
        rw [Category.assoc, ← P.w]; congr 1
        rw [← cancel_epi (τ s).hom, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, hτf]), ?_, ?_⟩, ?_, ?_⟩
    · apply P.hom_ext
      · rw [Category.assoc, P.lift_fst, ← Category.assoc, P.lift_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, P.lift_snd, P.lift_snd, Category.id_comp]
    · apply P.hom_ext
      · rw [Category.assoc, P.lift_fst, ← Category.assoc, P.lift_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, P.lift_snd, P.lift_snd, Category.id_comp]
    · exact P.lift_fst _ _ _
    · exact P.lift_snd _ _ _
  choose τ' hττ' hτ'f using τ'ex

  have hresι : ∀ (W : D₀.A.Opens) (hW : W ≤ k₀ ⁻¹ᵁ W), k₀.resLE W W hW ≫ W.ι = W.ι ≫ k₀ :=
    fun W hW => Scheme.Hom.resLE_comp_ι _ _
  have hgres : ∀ (W : D₀.A.Opens) (hW : W ≤ k₀ ⁻¹ᵁ W), (D₀.g ∣_ W) ≫ k₀.resLE W W hW = D₀.g ∣_ W := by
    intro W hW
    rw [← cancel_mono W.ι, Category.assoc, hresι, ← Category.assoc, morphismRestrict_ι, Category.assoc, hk₀g]

  have hcomm : ∀ i : 𝒰.ι, (k₀.resLE (𝒰.U i) (𝒰.U i) (hleU i) ≫ ι i) ≫ D.f =
      ((𝒰.U i).ι ≫ D₀.f) ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro i
    rw [Category.assoc, hιf, ← Category.assoc, hresι, Category.assoc, hk₀.w, Category.assoc]
  let ι' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ Dφ.A := fun i =>
    hh.lift (k₀.resLE (𝒰.U i) (𝒰.U i) (hleU i) ≫ ι i) ((𝒰.U i).ι ≫ D₀.f) (hcomm i)
  have hι'h : ∀ i, ι' i ≫ h = k₀.resLE (𝒰.U i) (𝒰.U i) (hleU i) ≫ ι i := fun i => hh.lift_fst _ _ _
  have hι'f : ∀ i, ι' i ≫ Dφ.f = (𝒰.U i).ι ≫ D₀.f := fun i => hh.lift_snd _ _ _

  have hsq : ∀ i, IsPullback (ι' i) (k₀.resLE (𝒰.U i) (𝒰.U i) (hleU i)) h (ι i) := by
    intro i
    refine IsPullback.of_right (h₁₂ := Dφ.f) (h₂₂ := D.f) (v₁₃ := Spec.map (CommRingCat.ofHom φ)) ?_ (hι'h i) hh.flip
    rw [hι'f, hιf]
    exact (cartW (𝒰.U i) (hleU i) (hk₀U i)).flip
  refine ⟨τ', hττ', hτ'f, ?_, ι', ?_, hι'f, ?_, ?_, ?_⟩
  ·
    intro s
    apply (cartW (𝒰.inter s) (hle s) (heqI s)).hom_ext
    · rw [Category.assoc, hττ', ← Category.assoc, hgres, hτg]
    · rw [Category.assoc, hτ'f]
  ·
    intro i
    haveI := hιo i
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hsq i).flip (hιo i)
  ·
    intro x
    obtain ⟨i, y, hy⟩ := hsurj (h.base x)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := ι i) x y (by simpa using hy.symm)
    refine ⟨i, (hsq i).isoPullback.inv.base z, ?_⟩
    have e1 : ((hsq i).isoPullback.inv ≫ ι' i).base z = x := by
      rw [IsPullback.isoPullback_inv_fst]; exact hz1
    exact e1
  ·
    intro i
    apply hh.hom_ext
    · rw [Category.assoc, hι'h, ← Category.assoc, hgres, hιg, Category.assoc, hhg]
    · rw [Category.assoc, hι'f, Category.assoc, Dφ.cart.w, ← Category.assoc, morphismRestrict_ι, Category.assoc,
        D₀.cart.w]
  ·
    intro s
    have hk₀le : ∀ (j : Fin 2), D₀.A.homOfLE (𝒰.inter_le s j) ≫ k₀.resLE (𝒰.U (s.1 j)) (𝒰.U (s.1 j)) (hleU (s.1 j)) =
        k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) ≫ D₀.A.homOfLE (𝒰.inter_le s j) := by
      intro j
      rw [← cancel_mono (𝒰.U (s.1 j)).ι, Category.assoc, hresι, ← Category.assoc, Scheme.homOfLE_ι, Category.assoc,
        Scheme.homOfLE_ι, hresι]
    apply hh.hom_ext
    · simp only [Category.assoc, hι'h]
      rw [← Category.assoc (D₀.A.homOfLE _), hk₀le, Category.assoc, hglue, ← Category.assoc (D₀.A.homOfLE _), hk₀le,
        Category.assoc, ← Category.assoc (τ' s).hom, hττ', Category.assoc]
    · simp only [Category.assoc, hι'f, Scheme.homOfLE_ι_assoc, hτ'f]

end S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq (solution)
