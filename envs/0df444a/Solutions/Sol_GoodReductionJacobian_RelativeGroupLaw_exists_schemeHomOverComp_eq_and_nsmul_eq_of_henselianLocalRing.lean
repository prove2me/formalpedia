-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dd67a373-0b38-5c7a-9e6c-2771b86ebaef

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing

set_option autoImplicit false

p2m_open "KaehlerDifferential Algebra TensorProduct Algebra.TensorProduct"

universe u

namespace R1NeronObjE5H

section algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem subsingleton_kaehler_of_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton Ω[T⁄S] := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    exact hex.apply_apply_eq_zero x
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    exact hex.apply_apply_eq_zero x
  rw [ha, hb]

theorem formallyEtale_of_formallySmooth_of_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  haveI hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  haveI : Algebra.FormallyUnramified S T := ⟨hΩ⟩

  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈
        LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      exact hex.apply_apply_eq_zero x
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem

  haveI hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  haveI : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  haveI : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

theorem mapBaseChange_surjective_of_formallyUnramified [Algebra.FormallyUnramified S T] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro y
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hy : KaehlerDifferential.map R S T T y = 0 := Subsingleton.elim _ _
  exact (hex y).mp hy

theorem bijective_of_surjective_of_finrank_eq {A : Type*} [CommRing A] [Nontrivial A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hrank : Module.finrank A M = Module.finrank A N) : Function.Bijective f := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf

theorem formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.FormallyEtale S T := by
  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine formallyEtale_of_formallySmooth_of_bijective (R := R) ?_
  have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
  cases subsingleton_or_nontrivial T with
  | inl hT =>
      exact ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
  | inr hT =>
      haveI : Nontrivial S := (algebraMap S T).domain_nontrivial
      have hS : Module.rank S Ω[S⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hTr : Module.rank T Ω[T⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
      have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
      exact bijective_of_surjective_of_finrank_eq _ hsurj
        (by rw [Module.finrank_baseChange, hSf, hTf])

theorem etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by
  haveI := formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n
  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end algebra

section ringHom

theorem ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : φ.IsStandardSmoothOfRelativeDimension n)
    (hψφ : (ψ.comp φ).IsStandardSmoothOfRelativeDimension n)
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  algebraize [φ, ψ, ψ.comp φ]
  exact R1NeronObjE5H.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n

theorem ringHom_etale_of_formallyUnramified_of_locally_isStandardSmoothOfRelativeDimension
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ)
    (hψφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (ψ.comp φ))
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  obtain ⟨sS, hsS, hS⟩ := hφ
  obtain ⟨sT, hsT, hT⟩ := hψφ

  let ι : Type u := sT × sS
  let g : ι → T := fun i => (i.1 : T) * ψ (i.2 : S)
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    have h1 : Ideal.span (ψ '' sS) = ⊤ := by
      have := congrArg (Ideal.map ψ) hsS
      rwa [Ideal.map_span, Ideal.map_top] at this
    have h2 : Ideal.span sT * Ideal.span (ψ '' sS) = Ideal.span (Set.range g) := by
      rw [Ideal.span_mul_span']
      congr 1
      ext x
      simp only [Set.mem_mul, Set.mem_image, Set.mem_range, g, ι, Prod.exists, Subtype.exists,
        exists_prop]
      constructor
      · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    rw [← h2, hsT, h1, Ideal.top_mul]

  let Tt : ι → Type u := fun i => Localization.Away (i.1 : T)
  let Tg : ι → Type u := fun i => Localization.Away (algebraMap T (Tt i) (ψ (i.2 : S)))
  have key : ∀ i : ι, RingHom.Etale ((algebraMap T (Tg i)).comp ψ) := by
    intro i
    obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := i
    let Ss := Localization.Away s
    have hunit : IsUnit ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ s) := by
      simp only [RingHom.coe_comp, Function.comp_apply, Tg]
      rw [IsScalarTower.algebraMap_apply T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (Tg (⟨t, ht⟩, ⟨s, hs⟩))]
      exact IsLocalization.Away.algebraMap_isUnit _

    let ψ' : Ss →+* Tg (⟨t, ht⟩, ⟨s, hs⟩) :=
      IsLocalization.Away.lift s (g := (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ) hunit
    have hψ' : ψ'.comp (algebraMap S Ss) = (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ := by
      ext x
      simp [ψ']

    have h1 : ((algebraMap S Ss).comp φ).IsStandardSmoothOfRelativeDimension n := hS s hs

    have h2 : ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp
        (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := by
      have h2a : ((algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩))).comp
          (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := hT t ht
      have := RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
      have h2b := this.2 (Tg (⟨t, ht⟩, ⟨s, hs⟩)) (algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (ψ s)) _ h2a
      rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h2b

    have h3 : ψ'.FormallyUnramified := by
      refine RingHom.FormallyUnramified.of_comp (f := algebraMap S Ss) ?_
      rw [hψ']
      exact RingHom.FormallyUnramified.comp hψ
        (RingHom.FormallyUnramified.holdsForLocalizationAway _ (t * ψ s))
    have h2' : (ψ'.comp ((algebraMap S Ss).comp φ)).IsStandardSmoothOfRelativeDimension n := by
      rwa [← RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    have h4 : ψ'.Etale :=
      R1NeronObjE5H.ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension n _ ψ'
        h1 h2' h3
    have h5 : (algebraMap S Ss).Etale := by
      rw [RingHom.etale_algebraMap]
      exact Algebra.Etale.of_isLocalizationAway s
    rw [← hψ']
    exact RingHom.Etale.stableUnderComposition _ _ h5 h4
  have hloc : RingHom.Locally RingHom.Etale ψ :=
    RingHom.locally_of_exists RingHom.Etale.respectsIso ψ g hspan Tg key
  exact (RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
    RingHom.Etale.ofLocalizationSpanTarget _).mp hloc

end ringHom

section scheme

open AlgebraicGeometry CategoryTheory

theorem scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension
    {X Y Z : Scheme.{u}} (n : ℕ) {f : X ⟶ Y} {g : Y ⟶ Z}
    (h1 : SmoothOfRelativeDimension n (f ≫ g)) (h2 : SmoothOfRelativeDimension n g)
    (h3 : FormallyUnramified f) : Etale f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H1 := IsZariskiLocalAtTarget.restrict h1 U.1
    rw [morphismRestrict_comp] at H1
    have H2 : SmoothOfRelativeDimension n (g ∣_ U.1) := IsZariskiLocalAtTarget.restrict h2 U.1
    have H3 : FormallyUnramified (f ∣_ g ⁻¹ᵁ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      (f ⁻¹ᵁ U.1).ι (f ≫ g) h1
    rw [← morphismRestrict_ι_assoc] at H1
    have H2 : SmoothOfRelativeDimension n (U.1.ι ≫ g) :=
      HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n) _ _ h2
    have H3 : FormallyUnramified (f ∣_ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      U.1.ι (f ≫ g) h1
    rw [← Category.assoc] at H1
    have H3 : FormallyUnramified (U.1.ι ≫ f) :=
      MorphismProperty.IsStableUnderComposition.comp_mem (P := @FormallyUnramified) _ _
        (inferInstance : FormallyUnramified U.1.ι) h3
    exact this H1 H3 U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)] at h1 h2
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)] at h3
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h1
  exact R1NeronObjE5H.ringHom_etale_of_formallyUnramified_of_locally_isStandardSmoothOfRelativeDimension
    n _ _ h2 h1 h3

end scheme

section groupLaw

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

theorem groupLaw_etale_schemeNsmul
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) := by
  have hu : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      G hcomm n hn
  have h1 : SmoothOfRelativeDimension d (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over]; infer_instance
  exact R1NeronObjE5H.scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension d h1 ‹_› hu

end groupLaw

end R1NeronObjE5H

namespace R1NeronObjE5

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem coe_nsmul_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem exists_nsmul_eq_of_etale [HenselianLocalRing R]
    (G : RelativeGroupLaw R f) (n : ℕ) [Etale (G.schemeNsmul n)]
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (y₀ : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) f)
    (hy₀ : G.nsmul _ n y₀ =
      GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
        (Category.comp_id _) x) :
    ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
          (Category.comp_id _) y = y₀ ∧
        G.nsmul _ n y = x := by

  haveI : Smooth (pullback.snd (G.schemeNsmul n) x.1) := inferInstance

  have hcomm : y₀.1 ≫ G.schemeNsmul n =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ x.1 := by
    have := congrArg Subtype.val hy₀
    rw [coe_nsmul_eq_comp_schemeNsmul] at this
    exact this
  have hz₀ : pullback.lift y₀.1 _ hcomm ≫ pullback.snd (G.schemeNsmul n) x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) :=
    pullback.lift_snd _ _ _

  obtain ⟨s, hs1, hs2⟩ :=
    AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
      (pullback.snd (G.schemeNsmul n) x.1) _ hz₀
  have hx1 : x.1 ≫ f = 𝟙 _ := x.2
  have hφf : G.schemeNsmul n ≫ f = f := G.schemeNsmul_over n
  refine ⟨⟨s ≫ pullback.fst (G.schemeNsmul n) x.1, ?_⟩, ?_, ?_⟩
  · calc (s ≫ pullback.fst (G.schemeNsmul n) x.1) ≫ f
        = s ≫ pullback.fst (G.schemeNsmul n) x.1 ≫ (G.schemeNsmul n ≫ f) := by
          rw [hφf, Category.assoc]
      _ = s ≫ (pullback.fst (G.schemeNsmul n) x.1 ≫ G.schemeNsmul n) ≫ f := by
          simp only [Category.assoc]
      _ = s ≫ (pullback.snd (G.schemeNsmul n) x.1 ≫ x.1) ≫ f := by rw [pullback.condition]
      _ = (s ≫ pullback.snd (G.schemeNsmul n) x.1) ≫ (x.1 ≫ f) := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hs1, hx1, Category.comp_id]
  · apply Subtype.ext
    show Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s ≫
        pullback.fst (G.schemeNsmul n) x.1 = y₀.1
    rw [← Category.assoc, hs2, pullback.lift_fst]
  · apply Subtype.ext
    rw [coe_nsmul_eq_comp_schemeNsmul]
    show (s ≫ pullback.fst (G.schemeNsmul n) x.1) ≫ G.schemeNsmul n = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]

end R1NeronObjE5

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : IsUnit (n : R))
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (y₀ : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) f)
    (hy₀ : G.nsmul _ n y₀ =
      GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
        (Category.comp_id _) x) :
    ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
          (Category.comp_id _) y = y₀ ∧
        G.nsmul _ n y = x := by
  haveI : Etale (G.schemeNsmul n) := R1NeronObjE5H.groupLaw_etale_schemeNsmul G hcomm d n hn
  exact R1NeronObjE5.exists_nsmul_eq_of_etale G n x y₀ hy₀

end S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing (solution)
