-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a36df46e-5abb-5c05-9f3d-cc7f0a52e2d8

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace

set_option autoImplicit false

noncomputable section

p2m_open "KaehlerDifferential Algebra TensorProduct Algebra.TensorProduct"

universe u

namespace R1NeronObjE8H

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
  exact R1NeronObjE8H.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
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
      R1NeronObjE8H.ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension n _ ψ'
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
  exact R1NeronObjE8H.ringHom_etale_of_formallyUnramified_of_locally_isStandardSmoothOfRelativeDimension
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
  exact R1NeronObjE8H.scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension d h1 ‹_› hu

end groupLaw

end R1NeronObjE8H

namespace R1NeronObjE8S

p2m_open "AlgebraicGeometry CategoryTheory RingHom Algebra.RingHom"

section descend

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

theorem appLE_basicOpen_basicOpen
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (h : P (f.appLE U V e).hom)
    (r : Γ(Y, U)) (s : Γ(X, X.basicOpen (f.appLE U V e r)))
    (e' : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r) :
    P (f.appLE (Y.basicOpen r) (X.basicOpen s) e').hom := by
  have ha : IsAffineOpen (X.basicOpen (f.appLE U V e r)) := V.2.basicOpen _
  haveI := V.2.isLocalization_basicOpen (f.appLE U V e r)
  haveI := U.2.isLocalization_basicOpen r
  haveI := ha.isLocalization_basicOpen s
  have heq : f.appLE (Y.basicOpen r) (X.basicOpen s) e' =
      f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  rw [heq]
  apply hPa _ s _
  rw [U.2.appLE_eq_away_map f V.2]
  exact hPl _ _ _ _ h

end descend

theorem eq_of_isStandardSmoothOfRelativeDimension_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {n n' : ℕ}
    (U : Y.affineOpens) (V : X.affineOpens) (hx : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n)
    (U' : Y.affineOpens) (V' : X.affineOpens) (hx' : x ∈ V'.1) (e' : V'.1 ≤ f ⁻¹ᵁ U'.1)
    (h' : (f.appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension n') : n = n' := by
  have hPa : ∀ m : ℕ, StableUnderCompositionWithLocalizationAwayTarget
      (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
  have hPl : ∀ m : ℕ, LocalizationAwayPreserves (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_localizationPreserves m).away

  obtain ⟨r, s, hxs, ers, hA⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n) (hPl n)
    x U' U V' V hx' hx e h (e' hx')
  let Br : Y.affineOpens := ⟨Y.basicOpen r, U'.2.basicOpen r⟩
  let Bs : X.affineOpens := ⟨X.basicOpen s, V'.2.basicOpen s⟩

  have hfx : f x ∈ Br.1 := ers hxs
  obtain ⟨r₂, s₂, hxs₂, ers₂, hB⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n')
    (hPl n') x Br U' Bs V' hxs hx' e' h' hfx

  let B' : X.Opens := X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
  have hle : X.basicOpen s₂ ≤ B' := by
    change X.basicOpen s₂ ≤ X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
    rw [Scheme.basicOpen_appLE]
    exact le_inf (X.basicOpen_le s₂) ers₂
  have hB'le : B' ≤ X.basicOpen s := X.basicOpen_le _
  let s₂' : Γ(X, B') := X.presheaf.map (homOfLE hB'le).op s₂
  have hBs₂ : X.basicOpen s₂' = X.basicOpen s₂ := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.mpr hle
  have ers₂' : X.basicOpen s₂' ≤ f ⁻¹ᵁ Y.basicOpen r₂ := hBs₂ ▸ ers₂
  have hC : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂')
      ers₂').hom.IsStandardSmoothOfRelativeDimension n :=
    appLE_basicOpen_basicOpen (hPa n) (hPl n) f Br Bs ers hA r₂ s₂' ers₂'
  have hC' : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂)
      ers₂).hom.IsStandardSmoothOfRelativeDimension n :=
    (f.appLE_congr ers₂' rfl hBs₂ (fun g => g.hom.IsStandardSmoothOfRelativeDimension n)).mp hC

  haveI : Nonempty (X.basicOpen s₂) := ⟨⟨x, hxs₂⟩⟩
  haveI : Nontrivial Γ(X, X.basicOpen s₂) := inferInstance
  algebraize [(f.appLE (Y.basicOpen r₂) (X.basicOpen s₂) ers₂).hom]
  have h1 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have h2 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n' :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n'
  exact_mod_cast h1.symm.trans h2

theorem exists_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, hfin, ⟨P⟩⟩ := hstd.out
  exact ⟨P.dimension, ⟨U, hU⟩, ⟨V, hV⟩, hx, e, ⟨⟨ι, σ, ‹_›, hfin, P, rfl⟩⟩⟩

theorem exists_smoothOfRelativeDimension_of_preconnectedSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [PreconnectedSpace X] : ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, ⟨fun x => (IsEmpty.false x).elim⟩⟩
  obtain ⟨n₀, U₀, V₀, hx₀, e₀, h₀⟩ := exists_chart f x₀
  let S : Set X := {x | ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n₀}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨U, V, hxV, e, h⟩
    exact ⟨V.1, fun y hy => ⟨U, V, hy, e, h⟩, V.1.isOpen, hxV⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hxS
    obtain ⟨m, U, V, hxV, e, h⟩ := exists_chart f x
    refine ⟨V.1, fun y hy hyS => ?_, V.1.isOpen, hxV⟩
    obtain ⟨U', V', hyV', e', h'⟩ := hyS
    have hm : m = n₀ :=
      eq_of_isStandardSmoothOfRelativeDimension_appLE f y U V hy e h U' V' hyV' e' h'
    subst hm
    exact hxS ⟨U, V, hxV, e, h⟩
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨x₀, U₀, V₀, hx₀, e₀, h₀⟩
  refine ⟨n₀, ⟨fun x => ?_⟩⟩
  have hxS : x ∈ S := hS ▸ Set.mem_univ x
  obtain ⟨U, V, hxV, e, h⟩ := hxS
  exact ⟨U.1, U.2, V.1, V.2, hxV, e, h⟩

end R1NeronObjE8S

namespace R1NeronObjE8

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

def basePt (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t f :=
  ⟨t ≫ g.1, by rw [Category.assoc, g.2, Category.comp_id]⟩

def transl (G : RelativeGroupLaw R f) (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    A ⟶ A :=
  (G.mul f (basePt g f) RelativeGroupLaw.idPoint).1

theorem comp_transl (G : RelativeGroupLaw R f) (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) :
    y.1 ≫ transl G g = (G.mul t (basePt g t) y).1 := by
  have h := G.mul_natural f t y.1 y.2 (basePt g f) RelativeGroupLaw.idPoint
  have h1 : GoodReductionJacobian.schemeHomOverComp y.1 y.2 (basePt g f) = basePt g t := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, basePt]
    rw [← Category.assoc, y.2]
  have h2 : GoodReductionJacobian.schemeHomOverComp y.1 y.2 (RelativeGroupLaw.idPoint (f := f)) = y :=
    Subtype.ext (Category.comp_id y.1)
  rw [h1, h2] at h
  exact (congrArg Subtype.val h)

theorem basePt_id (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    basePt g (𝟙 (Spec (CommRingCat.of R))) = g :=
  Subtype.ext (Category.id_comp g.1)

theorem basePt_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    basePt (G.one (𝟙 (Spec (CommRingCat.of R)))) t = G.one t := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem basePt_mul (G : RelativeGroupLaw R f)
    (g g' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    basePt (G.mul _ g g') t = G.mul t (basePt g t) (basePt g' t) :=
  G.mul_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t) g g'

theorem transl_one (G : RelativeGroupLaw R f) :
    transl G (G.one (𝟙 (Spec (CommRingCat.of R)))) = 𝟙 A := by
  unfold transl
  rw [basePt_one, G.one_mul]

theorem transl_comp_transl (G : RelativeGroupLaw R f)
    (g g' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl G g ≫ transl G g' = transl G (G.mul _ g' g) := by
  have h := comp_transl G g' f (G.mul f (basePt g f) RelativeGroupLaw.idPoint)
  change (G.mul f (basePt g f) RelativeGroupLaw.idPoint).1 ≫ transl G g' = _
  rw [h, transl, basePt_mul, G.mul_assoc]

theorem transl_leftInverse (G : RelativeGroupLaw R f)
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    Function.LeftInverse (transl G (G.inv _ g)) (transl G g) := by
  intro a
  change (transl G g ≫ transl G (G.inv _ g)) a = a
  rw [transl_comp_transl, G.inv_mul_cancel, transl_one]
  rfl

theorem transl_rightInverse (G : RelativeGroupLaw R f)
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    Function.RightInverse (transl G (G.inv _ g)) (transl G g) := by
  intro a
  change (transl G (G.inv _ g) ≫ transl G g) a = a
  rw [transl_comp_transl, G.mul_inv_cancel, transl_one]
  rfl

theorem isOpenMap_transl (G : RelativeGroupLaw R f)
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    IsOpenMap (transl G g) := by
  intro U hU
  rw [Set.image_eq_preimage_of_inverse (transl_leftInverse G g) (transl_rightInverse G g)]
  exact hU.preimage (transl G (G.inv _ g)).continuous

theorem nsmul_eq_pow (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, pow_succ, ih]; rfl

theorem nsmul_surjective {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} [Smooth f] [ConnectedSpace A]
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) :
    Function.Surjective (G.nsmul (𝟙 (Spec (CommRingCat.of K))) n) := by
  classical
  haveI : JacobsonSpace A := LocallyOfFiniteType.jacobsonSpace f

  obtain ⟨d, hd⟩ := R1NeronObjE8S.exists_smoothOfRelativeDimension_of_preconnectedSpace f
  haveI := hd
  haveI : Etale (G.schemeNsmul n) := R1NeronObjE8H.groupLaw_etale_schemeNsmul G hcomm d n hn
  have hopenφ : IsOpenMap (G.schemeNsmul n) := (G.schemeNsmul n).isOpenMap

  letI grp : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) :=
    { G.pointGroup _ with mul_comm := fun a b => hcomm _ a b }
  have hpow : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f, G.nsmul _ n y = y ^ n :=
    fun y => nsmul_eq_pow G _ n y

  let cp : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → A :=
    fun y => y.1 (IsLocalRing.closedPoint K)
  have hcp_closed : ∀ y, IsClosed ({cp y} : Set A) := fun y => (pointEquivClosedPoint f y).2
  have hcp_inj : Function.Injective cp := fun y y' h =>
    (pointEquivClosedPoint f).injective (Subtype.ext h)
  have hcp_surj : ∀ a : A, IsClosed ({a} : Set A) → ∃ y, cp y = a := fun a ha =>
    ⟨(pointEquivClosedPoint f).symm ⟨a, ha⟩, by simp [cp]⟩

  let ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → (A ⟶ A) :=
    fun g => G.schemeNsmul n ≫ transl G g
  have hψopen : ∀ g, IsOpen (Set.range (ψ g)) := by
    intro g
    have : (ψ g : A → A) = transl G g ∘ G.schemeNsmul n := by
      funext a; rfl
    rw [this]
    exact ((isOpenMap_transl G g).comp hopenφ).isOpen_range
  have hcpψ : ∀ g y, cp (g * G.nsmul _ n y) = ψ g (cp y) := by
    intro g y
    have h1 : (G.mul _ g (G.nsmul _ n y)).1 = y.1 ≫ ψ g := by
      have h2 := comp_transl G g (𝟙 (Spec (CommRingCat.of K))) (G.nsmul _ n y)
      rw [basePt_id] at h2
      rw [← h2, coe_nsmul_eq_comp_schemeNsmul, Category.assoc]
    show (G.mul _ g (G.nsmul _ n y)).1 (IsLocalRing.closedPoint K) =
      ψ g (y.1 (IsLocalRing.closedPoint K))
    rw [h1]
    rfl

  let S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) := Set.range (G.nsmul _ n)
  have hV : ∀ g (a : A), IsClosed ({a} : Set A) → a ∈ Set.range (ψ g) →
      ∃ y, cp (g * G.nsmul _ n y) = a := by
    rintro g a ha ⟨z₀, hz₀⟩
    obtain ⟨z, hzF, hzc⟩ := nonempty_inter_closedPoints (Z := (ψ g) ⁻¹' {a}) ⟨z₀, hz₀⟩
      ((ha.preimage (ψ g).continuous).isLocallyClosed)
    obtain ⟨y, hy⟩ := hcp_surj z hzc
    exact ⟨y, by rw [hcpψ, hy]; exact hzF⟩
  have hV' : ∀ g y, cp (g * G.nsmul _ n y) ∈ Set.range (ψ g) := fun g y => ⟨cp y, (hcpψ g y).symm⟩

  let O₁ : Set A := ⋃ g ∈ S, Set.range (ψ g)
  let O₂ : Set A := ⋃ g ∈ Sᶜ, Set.range (ψ g)
  have hO₁ : IsOpen O₁ := isOpen_biUnion fun g _ => hψopen g
  have hO₂ : IsOpen O₂ := isOpen_biUnion fun g _ => hψopen g
  have hcover : Set.univ ⊆ O₁ ∪ O₂ := by
    intro a _
    by_contra ha
    have hC : IsClosed (O₁ ∪ O₂)ᶜ := (hO₁.union hO₂).isClosed_compl
    obtain ⟨b, hbC, hbc⟩ :=
      nonempty_inter_closedPoints (Z := (O₁ ∪ O₂)ᶜ) ⟨a, ha⟩ hC.isLocallyClosed
    obtain ⟨y, rfl⟩ := hcp_surj b hbc
    have hy1 : cp y ∈ Set.range (ψ y) := by
      have := hV' y 1
      rwa [show G.nsmul _ n (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) = 1 from
        G.nsmul_unit _ n, mul_one] at this
    apply hbC
    by_cases hyS : y ∈ S
    · exact Or.inl (Set.mem_biUnion hyS hy1)
    · exact Or.inr (Set.mem_biUnion hyS hy1)
  have hdisj : Set.univ ∩ (O₁ ∩ O₂) = ∅ := by
    rw [Set.univ_inter, Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp1, hp2⟩
    obtain ⟨g, hgS, hpg⟩ := Set.mem_iUnion₂.mp hp1
    obtain ⟨g', hg'S, hpg'⟩ := Set.mem_iUnion₂.mp hp2
    have hopen : IsOpen (Set.range (ψ g) ∩ Set.range (ψ g')) := (hψopen g).inter (hψopen g')
    obtain ⟨c, ⟨hc1, hc2⟩, hcc⟩ :=
      nonempty_inter_closedPoints (Z := Set.range (ψ g) ∩ Set.range (ψ g')) ⟨p, hpg, hpg'⟩
        hopen.isLocallyClosed
    obtain ⟨y, hy⟩ := hV g c hcc hc1
    obtain ⟨y', hy'⟩ := hV g' c hcc hc2
    have heq : g * G.nsmul _ n y = g' * G.nsmul _ n y' := hcp_inj (hy.trans hy'.symm)
    obtain ⟨w, hw⟩ := hgS
    apply hg'S
    refine ⟨w * y * y'⁻¹, ?_⟩
    rw [hpow] at hw ⊢
    rw [hpow, hpow] at heq
    rw [mul_pow, mul_pow, inv_pow, hw, heq, mul_inv_cancel_right]
  rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ) O₁ O₂ hO₁ hO₂ hcover hdisj
    with h1 | h2
  · intro x
    obtain ⟨g, hgS, hxg⟩ := Set.mem_iUnion₂.mp (h1 (Set.mem_univ (cp x)))
    obtain ⟨y, hy⟩ := hV g (cp x) (hcp_closed x) hxg
    have hx : g * G.nsmul _ n y = x := hcp_inj hy
    obtain ⟨w, hw⟩ := hgS
    refine ⟨w * y, ?_⟩
    rw [hpow] at hw ⊢
    rw [hpow] at hx
    rw [mul_pow, hw, hx]
  · exfalso
    obtain ⟨g, hgS, hxg⟩ := Set.mem_iUnion₂.mp (h2 (Set.mem_univ (cp 1)))
    obtain ⟨y, hy⟩ := hV g (cp 1) (hcp_closed 1) hxg
    have h1' : g * G.nsmul _ n y = 1 := hcp_inj hy
    apply hgS
    refine ⟨y⁻¹, ?_⟩
    rw [hpow] at h1' ⊢
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_left h1').symm

end R1NeronObjE8

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    [Smooth f] [ConnectedSpace A]
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) :
    Function.Surjective (G.nsmul (𝟙 (Spec (CommRingCat.of K))) n) :=
  R1NeronObjE8.nsmul_surjective G hcomm n hn

end

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace (solution)
