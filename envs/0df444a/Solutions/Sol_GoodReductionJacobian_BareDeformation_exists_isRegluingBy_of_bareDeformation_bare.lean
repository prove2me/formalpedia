-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_bareDeformation_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4061f431-f0a6-5b8f-a553-8d291c4e6194

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_bareDeformation_bare

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

namespace G8aAux

open Opposite TopologicalSpace

theorem surjective_specMap (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hker : IsNilpotent (RingHom.ker π)) :
    Surjective (Spec.map (CommRingCat.ofHom π)) := by
  have hT : Nontrivial T := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨n, hn⟩ := hker
    have hk : RingHom.ker π = ⊤ := by
      ext x; simp [Subsingleton.elim (π x) 0]
    rw [hk, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top, Ideal.zero_eq_bot] at hn
    exact absurd hn top_ne_bot
  have hsub : Subsingleton (PrimeSpectrum T') := by
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    have hp := (IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime
    have hq := (IsArtinianRing.isPrime_iff_isMaximal q.asIdeal).mp q.isPrime
    rw [IsLocalRing.eq_maximalIdeal hp, IsLocalRing.eq_maximalIdeal hq]
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  exact ⟨fun p => ⟨(⟨m, hm.isPrime⟩ : PrimeSpectrum T), @Subsingleton.elim _ hsub _ _⟩⟩

theorem comp_base_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem ι_base_apply {X : Scheme.{0}} (U : X.Opens) (x : U) : U.ι.base x = x.1 := rfl

end G8aAux

open G8aAux Opposite TopologicalSpace in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover) (D : BareDeformation f₁ L₁ B) :
    ∃ τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)), D₀.IsRegluingBy 𝒰 τ D := by
  classical
  set ϖ := Spec.map (CommRingCat.ofHom (algebraMap B B₁)) with hϖ
  haveI : IsClosedImmersion ϖ := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : Surjective ϖ := surjective_specMap B B₁ (algebraMap B B₁) hker
  haveI : Smooth D.f := D.bundle.smooth
  haveI : Smooth D₀.f := D₀.bundle.smooth
  obtain ⟨hcl₀, hsurj₀, -⟩ := AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective ϖ D₀.cart
  obtain ⟨hcl, hsurj, -⟩ := AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective ϖ D.cart
  haveI := hcl₀
  haveI := hcl
  haveI := hsurj₀
  haveI := hsurj

  have hchart : ∀ i : 𝒰.ι, ∃ ιi : (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A,
      IsOpenImmersion ιi ∧ ιi ≫ D.f = (𝒰.U i).ι ≫ D₀.f ∧ (D₀.g ∣_ 𝒰.U i) ≫ ιi = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g := by
    intro i
    haveI : IsAffine (↑(𝒰.U i) : Scheme.{0}) := 𝒰.isAffineOpen i

    have hV : IsAffineOpen (D₀.g ⁻¹ᵁ 𝒰.U i) := (𝒰.isAffineOpen i).preimage D₀.g
    have hsqU : IsPullback (D₀.g ∣_ 𝒰.U i) ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ f₁) ((𝒰.U i).ι ≫ D₀.f) ϖ :=
      (isPullback_morphismRestrict D₀.g (𝒰.U i)).paste_vert D₀.cart

    obtain ⟨Z, hZ, γ, hγ, hsqZ⟩ := AlgebraicGeometry.exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
      (algebraMap B B₁) hπ hker D.f f₁ D.g D.cart (D₀.g ⁻¹ᵁ 𝒰.U i) hV
    haveI : IsAffine (↑Z : Scheme.{0}) := hZ

    obtain ⟨ℓ, hℓf, hℓg⟩ := AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
      (algebraMap B B₁) hπ hker ((𝒰.U i).ι ≫ D₀.f) (D₀.g ∣_ 𝒰.U i) ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ f₁) hsqU
      (Z.ι ≫ D.f) γ ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ f₁) hsqZ (𝟙 _) (Category.id_comp _)

    haveI : IsIso ℓ := AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker B B₁ (algebraMap B B₁) hπ hker
      ((𝒰.U i).ι ≫ D₀.f) (Z.ι ≫ D.f) ℓ hℓf ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ f₁) ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ f₁)
      (D₀.g ∣_ 𝒰.U i) hsqU γ hsqZ (𝟙 _) (by rw [hℓg]) (Category.id_comp _)
    refine ⟨ℓ ≫ Z.ι, inferInstance, by rw [Category.assoc, hℓf], ?_⟩
    rw [← Category.assoc, hℓg, Category.id_comp, hγ]
  choose ι hιopen hιf hιg using hchart

  have hιpt : ∀ (i : 𝒰.ι) (a : A₁) (ha : a ∈ D₀.g ⁻¹ᵁ 𝒰.U i),
      (ι i).base ((D₀.g ∣_ 𝒰.U i).base ⟨a, ha⟩) = D.g.base a := by
    intro i a ha
    have := congrArg (fun φ => φ.base ⟨a, ha⟩) (hιg i)
    exact this

  have hUpt : ∀ (i : 𝒰.ι) (y : (↑(𝒰.U i) : Scheme.{0})) (a : A₁) (ha : a ∈ D₀.g ⁻¹ᵁ 𝒰.U i),
      D₀.g.base a = y.1 → (D₀.g ∣_ 𝒰.U i).base ⟨a, ha⟩ = y := by
    intro i y a ha hay
    apply (𝒰.U i).ι.isOpenEmbedding.injective
    rw [← comp_base_apply, morphismRestrict_ι, comp_base_apply, ι_base_apply, ι_base_apply, hay]

  have hrange : ∀ s : 𝒰.Idx 1,
      ∀ w : (↑(𝒰.inter s) : Scheme.{0}),
        (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)).base w = (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)).base w := by
    intro s w
    obtain ⟨a, ha⟩ := D₀.g.surjective w.1
    have ha0 : a ∈ D₀.g ⁻¹ᵁ 𝒰.U (s.1 0) := by
      show D₀.g.base a ∈ (𝒰.U (s.1 0) : Set D₀.A); rw [ha]; exact 𝒰.inter_le s 0 w.2
    have ha1 : a ∈ D₀.g ⁻¹ᵁ 𝒰.U (s.1 1) := by
      show D₀.g.base a ∈ (𝒰.U (s.1 1) : Set D₀.A); rw [ha]; exact 𝒰.inter_le s 1 w.2
    have h0 : (D₀.A.homOfLE (𝒰.inter_le s 0)).base w = (D₀.g ∣_ 𝒰.U (s.1 0)).base ⟨a, ha0⟩ := by
      refine (hUpt _ _ a ha0 ?_).symm
      rw [ha, ← ι_base_apply (𝒰.U (s.1 0)), ← comp_base_apply, Scheme.homOfLE_ι]; rfl
    have h1 : (D₀.A.homOfLE (𝒰.inter_le s 1)).base w = (D₀.g ∣_ 𝒰.U (s.1 1)).base ⟨a, ha1⟩ := by
      refine (hUpt _ _ a ha1 ?_).symm
      rw [ha, ← ι_base_apply (𝒰.U (s.1 1)), ← comp_base_apply, Scheme.homOfLE_ι]; rfl
    rw [comp_base_apply, comp_base_apply, h0, h1, hιpt, hιpt]
  have hsub01 : ∀ s : 𝒰.Idx 1,
      Set.range (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)).base ⊆ Set.range (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)).base := by
    intro s; rintro _ ⟨w, rfl⟩; exact ⟨w, (hrange s w).symm⟩
  have hsub10 : ∀ s : 𝒰.Idx 1,
      Set.range (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)).base ⊆ Set.range (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)).base := by
    intro s; rintro _ ⟨w, rfl⟩; exact ⟨w, hrange s w⟩
  haveI hoi : ∀ (s : 𝒰.Idx 1) (j : Fin 2), IsOpenImmersion (D₀.A.homOfLE (𝒰.inter_le s j) ≫ ι (s.1 j)) :=
    fun s j => by haveI := hιopen (s.1 j); infer_instance
  let τh : ∀ s : 𝒰.Idx 1, (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s) := fun s =>
    IsOpenImmersion.lift (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)) (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)) (hsub01 s)
  let τi : ∀ s : 𝒰.Idx 1, (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s) := fun s =>
    IsOpenImmersion.lift (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)) (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)) (hsub10 s)
  have hτh : ∀ s, τh s ≫ (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)) = D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0) :=
    fun s => IsOpenImmersion.lift_fac _ _ _
  have hτi : ∀ s, τi s ≫ (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)) = D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1) :=
    fun s => IsOpenImmersion.lift_fac _ _ _
  let τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)) := fun s =>
    { hom := τh s
      inv := τi s
      hom_inv_id := by
        rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)), Category.assoc, hτi, hτh, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)), Category.assoc, hτh, hτi, Category.id_comp] }
  refine ⟨τ, ?_, ?_, ι, hιopen, hιf, ?_, hιg, fun s => (hτh s).symm⟩
  ·
    intro s
    have e1 : (𝒰.inter s).ι ≫ D₀.f = (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)) ≫ D.f := by
      rw [Category.assoc, hιf, ← Category.assoc, Scheme.homOfLE_ι]
    have e0 : (𝒰.inter s).ι ≫ D₀.f = (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0)) ≫ D.f := by
      rw [Category.assoc, hιf, ← Category.assoc, Scheme.homOfLE_ι]
    show τh s ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f
    conv_lhs => rw [e1]
    rw [← Category.assoc, hτh, ← e0]
  ·
    intro s
    show (D₀.g ∣_ 𝒰.inter s) ≫ τh s = D₀.g ∣_ 𝒰.inter s
    rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1)), Category.assoc, hτh]

    have key : ∀ j : Fin 2, (D₀.g ∣_ 𝒰.inter s) ≫ D₀.A.homOfLE (𝒰.inter_le s j) ≫ ι (s.1 j) = (D₀.g ⁻¹ᵁ 𝒰.inter s).ι ≫ D.g := by
      intro j
      have hres : (D₀.g ∣_ 𝒰.inter s) ≫ D₀.A.homOfLE (𝒰.inter_le s j) =
          A₁.homOfLE (D₀.g.preimage_mono (𝒰.inter_le s j)) ≫ (D₀.g ∣_ 𝒰.U (s.1 j)) := by
        rw [← cancel_mono (𝒰.U (s.1 j)).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
      rw [← Category.assoc, hres, Category.assoc, hιg, ← Category.assoc, Scheme.homOfLE_ι]
    rw [key 0, key 1]
  ·
    intro x
    obtain ⟨a, rfl⟩ := D.g.surjective x
    have hmem : D₀.g.base a ∈ (⨆ i, 𝒰.U i) := by rw [𝒰.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hmem
    exact ⟨i, (D₀.g ∣_ 𝒰.U i).base ⟨a, hi⟩, hιpt i a hi⟩

end S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_bareDeformation_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_bareDeformation_bare (solution)
