-- Prove2me | solution 1 for NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8568e8a2-6ca2-55e0-9871-4a9aab62d0cc

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace GoodLocalises29

open TensorProduct

theorem core_smooth {R k A A' : Type u} [CommRing R] [CommRing k] [CommRing A] [CommRing A']
    [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] (h : A) [IsLocalization.Away h A']
    (J : Ideal A) (J' : Ideal A') (hJ' : J' = J.map (algebraMap A A')) (hle : J ≤ J'.comap (algebraMap A A'))
    (φ : k →+* A ⧸ J) (hφ : φ.comp (algebraMap R k) = algebraMap R (A ⧸ J))
    (𝔮' : Ideal (A' ⧸ J')) [𝔮'.IsPrime]
    (hsm : ∀ [Algebra k (A ⧸ J)] [IsScalarTower R k (A ⧸ J)],
      Algebra.IsSmoothAt k (𝔮'.comap (Ideal.quotientMap J' (algebraMap A A') hle)))
    [Algebra k (A' ⧸ J')] [IsScalarTower R k (A' ⧸ J')] :
    Algebra.IsSmoothAt k 𝔮' := by
  classical
  set ι : A ⧸ J →+* A' ⧸ J' := Ideal.quotientMap J' (algebraMap A A') hle with hι
  letI algBB' : Algebra (A ⧸ J) (A' ⧸ J') := ι.toAlgebra
  have hιalg : algebraMap (A ⧸ J) (A' ⧸ J') = ι := rfl
  haveI : IsScalarTower A (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hιalg, hι, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl
  haveI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ J), IsScalarTower.algebraMap_apply R A' (A' ⧸ J'),
      IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A (A ⧸ J) (A' ⧸ J'),
      IsScalarTower.algebraMap_apply A A' (A' ⧸ J')]

  haveI hloc : IsLocalization.Away (algebraMap A (A ⧸ J) h) (A' ⧸ J') := by
    have := IsLocalization.of_surjective (.powers h) A' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
      (by ext a; rw [RingHom.comp_apply, RingHom.comp_apply, hιalg, hι, Ideal.quotientMap_mk])
      (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ'])
    rwa [Submonoid.map_powers] at this

  letI : Algebra k (A ⧸ J) := φ.toAlgebra
  haveI : IsScalarTower R k (A ⧸ J) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, hφ]
  haveI : IsScalarTower k (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨r, rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply R k (A' ⧸ J'), ← IsScalarTower.algebraMap_apply R k (A ⧸ J),
      ← IsScalarTower.algebraMap_apply R (A ⧸ J) (A' ⧸ J')]
  have hmem : (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈ Algebra.smoothLocus k (A' ⧸ J') := by
    rw [← Algebra.smoothLocus_comap_of_isLocalization (R := k) (algebraMap A (A ⧸ J) h), Set.mem_preimage]
    change Algebra.IsSmoothAt k (𝔮'.comap (algebraMap (A ⧸ J) (A' ⧸ J')))
    exact hsm
  exact hmem

theorem core_free {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] (h : A) [IsLocalization.Away h A']
    (J : Ideal A) (J' : Ideal A') (hJ' : J' = J.map (algebraMap A A')) (hle : J ≤ J'.comap (algebraMap A A'))
    (𝔮' : Ideal (A' ⧸ J')) [𝔮'.IsPrime]
    (hfr : (⟨𝔮'.comap (Ideal.quotientMap J' (algebraMap A A') hle), inferInstance⟩ :
        PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈ Module.freeLocus (A' ⧸ J') ((A' ⧸ J') ⊗[A'] Ω[A'⁄R]) := by
  classical
  set ι : A ⧸ J →+* A' ⧸ J' := Ideal.quotientMap J' (algebraMap A A') hle with hι
  letI algBB' : Algebra (A ⧸ J) (A' ⧸ J') := ι.toAlgebra
  have hιalg : algebraMap (A ⧸ J) (A' ⧸ J') = ι := rfl
  haveI : IsScalarTower A (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hιalg, hι, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl
  haveI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ J), IsScalarTower.algebraMap_apply R A' (A' ⧸ J'),
      IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A (A ⧸ J) (A' ⧸ J'),
      IsScalarTower.algebraMap_apply A A' (A' ⧸ J')]

  haveI hloc : IsLocalization.Away (algebraMap A (A ⧸ J) h) (A' ⧸ J') := by
    have := IsLocalization.of_surjective (.powers h) A' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
      (by ext a; rw [RingHom.comp_apply, RingHom.comp_apply, hιalg, hι, Ideal.quotientMap_mk])
      (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ'])
    rwa [Submonoid.map_powers] at this

  have h1 : (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈
      Module.freeLocus (A' ⧸ J') ((A' ⧸ J') ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R])) :=
    Module.comap_freeLocus_le (Set.mem_preimage.mpr hfr)

  have hbc : IsBaseChange A' (KaehlerDifferential.map R R A A') :=
    (isLocalizedModule_iff_isBaseChange (.powers h) A' _).mp inferInstance
  let e₁ := AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A' ⧸ J') (A' ⧸ J') Ω[A⁄R]
  let e₂ := (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ J') (A' ⧸ J') Ω[A⁄R]).symm
  let e₃ : (A' ⧸ J') ⊗[A'] (A' ⊗[A] Ω[A⁄R]) ≃ₗ[A' ⧸ J'] (A' ⧸ J') ⊗[A'] Ω[A'⁄R] :=
    AlgebraTensorModule.congr (LinearEquiv.refl (A' ⧸ J') (A' ⧸ J')) hbc.equiv
  rw [Module.freeLocus_congr (e₁.trans (e₂.trans e₃))] at h1
  exact h1

end GoodLocalises29

namespace GoodLoc29

theorem comap_primeIdealOf_basicOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U))
    (z : X) (hz : z ∈ U) (hz' : z ∈ X.basicOpen h) :
    ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩).asIdeal.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) =
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  have key : PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩) =
      hU.primeIdealOf ⟨z, hz⟩ := by
    rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint, IsAffineOpen.primeIdealOf_eq_map_closedPoint]
    change (Spec.map (X.presheaf.germ (X.basicOpen h) z hz') ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, X.basicOpen h)))).base
        (IsLocalRing.closedPoint _) = _
    rw [← Spec.map_comp]
    have hg : CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) ≫ X.presheaf.germ (X.basicOpen h) z hz' =
        X.presheaf.germ U z hz :=
      TopCat.Presheaf.germ_res X.presheaf (homOfLE (X.basicOpen_le h)) z hz'
    rw [hg]
  exact congrArg PrimeSpectrum.asIdeal key

theorem algebraMap_mem_primeIdealOf_of_mem_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) (z : U) (hz : f z.1 = IsLocalRing.closedPoint R)
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    algebraMap R Γ(X, U) r ∈ (hU.primeIdealOf z).asIdeal := by

  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at hsq

  have h1 := congrArg (fun g : Spec Γ(X, U) ⟶ Spec (CommRingCat.of R) => g.base (hU.primeIdealOf z)) hsq
  have h1' : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv).base ((Spec.map (f.appLE ⊤ U le_top)).base (hU.primeIdealOf z)) =
      f.base (hU.fromSpec.base (hU.primeIdealOf z)) := h1
  rw [hU.fromSpec_primeIdealOf] at h1'
  replace h1 := h1'.trans hz

  have h2 : r ∈ (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (PrimeSpectrum.comap (f.appLE ⊤ U le_top).hom (hU.primeIdealOf z))).asIdeal := by
    have : (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (PrimeSpectrum.comap (f.appLE ⊤ U le_top).hom (hU.primeIdealOf z))) = IsLocalRing.closedPoint R := h1
    rw [this]
    exact hr
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap] at h2
  have happ : (f.appLE ⊤ U le_top).hom = (X.presheaf.map (homOfLE le_top).op).hom.comp f.appTop.hom := by
    have : f.appLE ⊤ U le_top = f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [this, CommRingCat.hom_comp]
  rw [happ] at h2
  exact h2

end GoodLoc29

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (C : Set X) (hC : ∀ y ∈ C, f y = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) (h : Γ(X, U)) (y : X) (hyU : y ∈ U) (hyh : y ∈ X.basicOpen h) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    letI : Algebra R Γ(X, X.basicOpen h) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
    let J' : Ideal Γ(X, X.basicOpen h) :=
      PrimeSpectrum.vanishingIdeal ((fun z : X.basicOpen h => (hU.basicOpen h).primeIdealOf z) ''
        {z : X.basicOpen h | (z : X) ∈ C})
    (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
      𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
      (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
        Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) →
    ∀ (𝔮' : Ideal (Γ(X, X.basicOpen h) ⧸ J')) [𝔮'.IsPrime],
      𝔮'.comap (Ideal.Quotient.mk J') = ((hU.basicOpen h).primeIdealOf ⟨y, hyh⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮') ∧
      (⟨𝔮', ‹_›⟩ : PrimeSpectrum (Γ(X, X.basicOpen h) ⧸ J')) ∈
        Module.freeLocus (Γ(X, X.basicOpen h) ⧸ J')
          ((Γ(X, X.basicOpen h) ⧸ J') ⊗[Γ(X, X.basicOpen h)] Ω[Γ(X, X.basicOpen h)⁄R]) := by
  intro J J' hgood 𝔮' _ h𝔮'
  classical
  letI algA : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  letI algA' : Algebra R Γ(X, X.basicOpen h) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

  haveI : IsLocalization.Away h Γ(X, X.basicOpen h) := hU.isLocalization_basicOpen h
  have halg : ∀ t : Γ(X, U), algebraMap Γ(X, U) Γ(X, X.basicOpen h) t = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom t :=
    fun t => rfl
  haveI : IsScalarTower R Γ(X, U) Γ(X, X.basicOpen h) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg]
    show (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom
        ((X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE le_top).op) (X.presheaf.map (homOfLE (X.basicOpen_le h)).op),
      ← X.presheaf.map_comp]
    rfl

  have hS2 : ∀ (z : X) (hz : z ∈ U) (hz' : z ∈ X.basicOpen h),
      ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩).asIdeal.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) =
        (hU.primeIdealOf ⟨z, hz⟩).asIdeal := GoodLoc29.comap_primeIdealOf_basicOpen hU h
  have hbo : ∀ (z : X) (hz : z ∈ U), z ∉ X.basicOpen h → h ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
    intro z hz hzh
    by_contra hh
    apply hzh
    have h1 : hU.primeIdealOf ⟨z, hz⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hh
    have h2 : hU.fromSpec (hU.primeIdealOf ⟨z, hz⟩) ∈ X.basicOpen h := h1
    rwa [hU.fromSpec_primeIdealOf] at h2

  have hJle : J ≤ J'.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) := by
    intro g hg
    rw [Ideal.mem_comap]
    change _ ∈ PrimeSpectrum.vanishingIdeal _
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro _ ⟨⟨z, hz'⟩, hzC, rfl⟩
    have hzU : z ∈ U := X.basicOpen_le h hz'
    rw [← Ideal.mem_comap, hS2 z hzU hz']
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg _ ⟨⟨z, hzU⟩, hzC, rfl⟩
  have hJ' : J' = J.map (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) := by
    apply le_antisymm _ (Ideal.map_le_iff_le_comap.mpr hJle)
    intro g' hg'
    obtain ⟨⟨g, s⟩, hgs⟩ := IsLocalization.surj (Submonoid.powers h) g'
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h)]
    refine ⟨⟨⟨g * h, ?_⟩, ⟨(s : Γ(X, U)) * h, Submonoid.mul_mem _ s.2 (Submonoid.mem_powers h)⟩⟩, ?_⟩
    · change g * h ∈ PrimeSpectrum.vanishingIdeal _
      rw [PrimeSpectrum.mem_vanishingIdeal]
      rintro _ ⟨⟨z, hzU⟩, hzC, rfl⟩
      by_cases hz' : z ∈ X.basicOpen h
      · have h1 : algebraMap Γ(X, U) Γ(X, X.basicOpen h) g ∈ ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩).asIdeal := by
          rw [← hgs]
          exact Ideal.mul_mem_right _ _ ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hg' _ ⟨⟨z, hz'⟩, hzC, rfl⟩)
        rw [← Ideal.mem_comap, hS2 z hzU hz'] at h1
        exact Ideal.mul_mem_right _ _ h1
      · exact Ideal.mul_mem_left _ _ (hbo z hzU hz')
    · change g' * algebraMap Γ(X, U) Γ(X, X.basicOpen h) ((s : Γ(X, U)) * h) = algebraMap Γ(X, U) Γ(X, X.basicOpen h) (g * h)
      rw [map_mul, map_mul, ← hgs, mul_assoc]

  set ι' : Γ(X, U) ⧸ J →+* Γ(X, X.basicOpen h) ⧸ J' :=
    Ideal.quotientMap J' (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) hJle with hι'
  haveI : (𝔮'.comap ι').IsPrime := Ideal.comap_isPrime ι' 𝔮'
  have h𝔮 : (𝔮'.comap ι').comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [Ideal.comap_comap, hι', Ideal.quotientMap_comp_mk hJle, ← Ideal.comap_comap, h𝔮', hS2 y hyU hyh]
  obtain ⟨hsm, hfr⟩ := hgood (𝔮'.comap ι') h𝔮

  have hmJ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R Γ(X, U) r ∈ J := by
    intro r hr
    change _ ∈ PrimeSpectrum.vanishingIdeal _
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro _ ⟨z, hzC, rfl⟩
    exact GoodLoc29.algebraMap_mem_primeIdealOf_of_mem_maximalIdeal f hU z (hC _ hzC) r hr
  let φ : IsLocalRing.ResidueField R →+* Γ(X, U) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (Γ(X, U) ⧸ J)) (fun r hr => by
      rw [IsScalarTower.algebraMap_apply R Γ(X, U) (Γ(X, U) ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hmJ r hr)
  have hφ : φ.comp (algebraMap R (IsLocalRing.ResidueField R)) = algebraMap R (Γ(X, U) ⧸ J) := by
    ext r; rfl
  have hk : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_⟩
  · intro instK instT
    exact GoodLocalises29.core_smooth hk h J J' hJ' hJle φ hφ 𝔮' hsm
  · exact GoodLocalises29.core_free (R := R) h J J' hJ' hJle 𝔮' hfr

end S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
end P2MW
export P2MW.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus (solution)
