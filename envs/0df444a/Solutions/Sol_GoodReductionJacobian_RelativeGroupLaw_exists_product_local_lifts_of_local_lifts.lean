-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_product_local_lifts_of_local_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b5244f0d-8324-5232-a050-350dd6f0df9f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_isAffineHom_and_isPullback_pullback_lift_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem N0aAux.surjective_specMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ f hf]
    refine (PrimeSpectrum.mem_zeroLocus x _).mpr ?_
    intro t ht
    obtain ⟨n, hn⟩ := hnil t ht
    exact x.2.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]
    (L₀ : RelativeGroupLaw T f₀)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (hLk : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i₀ =
        (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨P.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, Q.2]⟩).1)
    (𝒲 : (pullback fk fk).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ (𝒰.comap i₀).U (lam₃ w)) :
    ∃
      (_ : IsAffineHom (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])))
      (_ : IsPullback (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
            (pullback.fst fk fk ≫ fk) (pullback.fst f₀ f₀ ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)))

      (Vop : 𝒲.ι → (pullback f₀ f₀).Opens) (_ : ∀ w, IsAffineOpen (Vop w)) (_ : ⨆ w, Vop w = ⊤)
      (_ : ∀ w, (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (Vop w) = 𝒲.U w)
      (hV₁ : ∀ w, Vop w ≤ pullback.fst f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₁ w))
      (hV₂ : ∀ w, Vop w ≤ pullback.snd f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₂ w))
      (hV₃ : ∀ w, Vop w ≤ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒰.U (lam₃ w))

      (Z : 𝒲.ι → Scheme.{u}) (qZ : ∀ w, Z w ⟶ Spec (CommRingCat.of T')) (_ : ∀ w, IsAffine (Z w)) (_ : ∀ w, Smooth (qZ w))
      (gZ : ∀ w, (↑(Vop w) : Scheme.{u}) ⟶ Z w)
      (_ : ∀ w, IsPullback (gZ w) ((Vop w).ι ≫ pullback.fst f₀ f₀ ≫ f₀) (qZ w) (Spec.map (CommRingCat.ofHom π)))

      (hZ₁ : ∀ w, Z w ⟶ Y (lam₁ w)) (hZ₂ : ∀ w, Z w ⟶ Y (lam₂ w)) (hZ₃ : ∀ w, Z w ⟶ Y (lam₃ w)),
      (∀ w, hZ₁ w ≫ q (lam₁ w) = qZ w ∧ gZ w ≫ hZ₁ w = (pullback f₀ f₀).homOfLE (hV₁ w) ≫ (pullback.fst f₀ f₀ ∣_ 𝒰.U (lam₁ w)) ≫ g (lam₁ w)) ∧
      (∀ w, hZ₂ w ≫ q (lam₂ w) = qZ w ∧ gZ w ≫ hZ₂ w = (pullback f₀ f₀).homOfLE (hV₂ w) ≫ (pullback.snd f₀ f₀ ∣_ 𝒰.U (lam₂ w)) ≫ g (lam₂ w)) ∧
      (∀ w, hZ₃ w ≫ q (lam₃ w) = qZ w ∧
        gZ w ≫ hZ₃ w = (pullback f₀ f₀).homOfLE (hV₃ w) ≫ ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ∣_ 𝒰.U (lam₃ w)) ≫ g (lam₃ w)) := by
  classical

  obtain ⟨hPaff, hPcart⟩ :=
    AlgebraicGeometry.isAffineHom_and_isPullback_pullback_lift_of_isPullback ρ f₀ fk i₀ hi₀

  have hρs : Function.Surjective ρ := by
    have : Function.Surjective (ρ.comp π) := by rw [hρ]; exact Ideal.Quotient.mk_surjective
    exact Function.Surjective.of_comp this
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ)) := IsClosedImmersion.spec_of_surjective _ hρs
  haveI hsurjρ : Surjective (Spec.map (CommRingCat.ofHom ρ)) := by
    refine N0aAux.surjective_specMap ρ hρs (fun t ht => ?_)
    obtain ⟨t', rfl⟩ := hπ t
    have h1 : residue T' t' = 0 := by
      have := RingHom.mem_ker.mp ht
      rwa [← RingHom.comp_apply, hρ] at this
    have h2 : t' ∈ maximalIdeal T' := (IsLocalRing.residue_eq_zero_iff _).mp h1
    have h3 : IsNilpotent (maximalIdeal T') := by
      have := IsArtinianRing.isNilpotent_jacobson_bot (R := T')
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
    obtain ⟨n, hn⟩ := h3
    refine ⟨n, ?_⟩
    have : t' ^ n ∈ maximalIdeal T' ^ n := Ideal.pow_mem_pow h2 n
    rw [hn] at this
    rw [← map_pow, (Submodule.mem_bot _).mp this, map_zero]
  haveI : IsClosedImmersion (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) := MorphismProperty.of_isPullback hPcart.flip inferInstance
  haveI : Surjective (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) := MorphismProperty.of_isPullback hPcart.flip inferInstance

  obtain ⟨Vop, hVaff, hVcov, hVpre, hVle⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_preimage_eq_of_isClosedImmersion_of_surjective (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) 𝒲
  have hjP1 : (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ pullback.fst f₀ f₀ = pullback.fst fk fk ≫ i₀ := pullback.lift_fst _ _ _
  have hjP2 : (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ pullback.snd f₀ f₀ = pullback.snd fk fk ≫ i₀ := pullback.lift_snd _ _ _
  have hjP3 : (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 = (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ≫ i₀ := by
    have hψ : (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ (pullback.fst f₀ f₀ ≫ f₀) =
        (pullback.fst fk fk ≫ fk) ≫ Spec.map (CommRingCat.ofHom ρ) := hPcart.w
    have hn := L₀.mul_natural (pullback.fst f₀ f₀ ≫ f₀) _ _ hψ
      ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩
    have hP : schemeHomOverComp _ hψ (⟨pullback.fst f₀ f₀, rfl⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) =
        ⟨pullback.fst fk fk ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc]⟩ :=
      Subtype.ext (by rw [schemeHomOverComp_coe]; exact hjP1)
    have hQ : schemeHomOverComp _ hψ (⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) =
        ⟨pullback.snd fk fk ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, pullback.condition]⟩ :=
      Subtype.ext (by rw [schemeHomOverComp_coe]; exact hjP2)
    calc _ = (schemeHomOverComp _ hψ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩
              ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩)).1 := (schemeHomOverComp_coe _ _ _).symm
      _ = _ := by rw [hn, hP, hQ]
      _ = _ := (hLk _ _ _).symm
  have hV₁ : ∀ w, Vop w ≤ pullback.fst f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₁ w) := fun w =>
    hVle _ w (by rw [← Scheme.Hom.comp_preimage, hjP1, Scheme.Hom.comp_preimage]; exact h₁ w)
  have hV₂ : ∀ w, Vop w ≤ pullback.snd f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₂ w) := fun w =>
    hVle _ w (by rw [← Scheme.Hom.comp_preimage, hjP2, Scheme.Hom.comp_preimage]; exact h₂ w)
  have hV₃ : ∀ w, Vop w ≤ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒰.U (lam₃ w) := fun w =>
    hVle _ w (by rw [← Scheme.Hom.comp_preimage, hjP3, Scheme.Hom.comp_preimage]; exact h₃ w)

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI hsurjπ : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine N0aAux.surjective_specMap π hπ (fun x hx => ?_)
    obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩
    have hx' : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hx'
    exact (Submodule.mem_bot _).mp hx'
  have hYaff : ∀ a, IsAffine (Y a) := by
    intro a
    haveI : IsClosedImmersion (g a) := MorphismProperty.of_isPullback (hg a).flip inferInstance
    haveI : Surjective (g a) := MorphismProperty.of_isPullback (hg a).flip inferInstance
    haveI : IsAffine (↑(𝒰.U a) : Scheme.{u}) := 𝒰.isAffineOpen a
    exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective (g a)

  have hm₀ : (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ f₀ = pullback.fst f₀ f₀ ≫ f₀ :=
    (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).2
  have hw : ∀ w : 𝒲.ι, ∃ (Z : Scheme.{u}) (qZ : Z ⟶ Spec (CommRingCat.of T')) (_ : IsAffine Z) (_ : Smooth qZ)
      (gZ : (↑(Vop w) : Scheme.{u}) ⟶ Z)
      (_ : IsPullback gZ ((Vop w).ι ≫ pullback.fst f₀ f₀ ≫ f₀) qZ (Spec.map (CommRingCat.ofHom π)))
      (hZ₁ : Z ⟶ Y (lam₁ w)) (hZ₂ : Z ⟶ Y (lam₂ w)) (hZ₃ : Z ⟶ Y (lam₃ w)),
      (hZ₁ ≫ q (lam₁ w) = qZ ∧ gZ ≫ hZ₁ = (pullback f₀ f₀).homOfLE (hV₁ w) ≫ (pullback.fst f₀ f₀ ∣_ 𝒰.U (lam₁ w)) ≫ g (lam₁ w)) ∧
      (hZ₂ ≫ q (lam₂ w) = qZ ∧ gZ ≫ hZ₂ = (pullback f₀ f₀).homOfLE (hV₂ w) ≫ (pullback.snd f₀ f₀ ∣_ 𝒰.U (lam₂ w)) ≫ g (lam₂ w)) ∧
      (hZ₃ ≫ q (lam₃ w) = qZ ∧
        gZ ≫ hZ₃ = (pullback f₀ f₀).homOfLE (hV₃ w) ≫ ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ∣_ 𝒰.U (lam₃ w)) ≫ g (lam₃ w)) := by
    intro w
    obtain ⟨Z, qZ, hZaff, hZs, gZ, hgZ, k₁, k₂, hk₁, hk₂⟩ :=
      AlgebraicGeometry.Smooth.exists_affine_smooth_local_lift_opens_pullback π hπ hker f₀ (𝒰.U (lam₁ w)) (𝒰.U (lam₂ w))
        (Y (lam₁ w)) (Y (lam₂ w)) (q (lam₁ w)) (q (lam₂ w)) (hq (lam₁ w)) (hq (lam₂ w)) (g (lam₁ w)) (g (lam₂ w))
        (hg (lam₁ w)) (hg (lam₂ w)) (Vop w) (hVaff w) (hV₁ w) (hV₂ w)
    haveI := hZaff; haveI := hYaff (lam₃ w); haveI := hq (lam₃ w)
    obtain ⟨k₃, hk₃q, hk₃g⟩ :=
      AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent π hπ hker qZ gZ
        ((Vop w).ι ≫ pullback.fst f₀ f₀ ≫ f₀) hgZ (q (lam₃ w)) (g (lam₃ w)) ((𝒰.U (lam₃ w)).ι ≫ f₀) (hg (lam₃ w))
        ((pullback f₀ f₀).homOfLE (hV₃ w) ≫ ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ∣_ 𝒰.U (lam₃ w))) (by
          rw [Category.assoc, morphismRestrict_ι_assoc, hm₀, ← Category.assoc, Scheme.homOfLE_ι])
    exact ⟨Z, qZ, hZaff, hZs, gZ, hgZ, k₁, k₂, k₃, hk₁, hk₂, hk₃q, hk₃g⟩
  choose Z qZ hZaff hZs gZ hgZ hZ₁ hZ₂ hZ₃ hE1 hE2 hE3 using hw
  exact ⟨hPaff, hPcart, Vop, hVaff, hVcov, hVpre, hV₁, hV₂, hV₃, Z, qZ, hZaff, hZs, gZ, hgZ, hZ₁, hZ₂, hZ₃, hE1, hE2, hE3⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts (solution)
