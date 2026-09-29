-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/db110eef-d45f-5fcc-8d5a-e36adc9304eb

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (U₁ : (pullback z f).Opens) (hηU₁ : η ∈ U₁) (h₁ : U₁ ≤ U₀)
    (hv : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v))
    (hyτ : τ₀.1.base ⟨η, hηU⟩ = T.y)
    (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f)
    (hε : IsOpenImmersion ε.1) (hεy : ε.1.base ⟨T.y, hyW⟩ = (D.C c).y)
    (hεchart : (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
      IsOpenImmersion
        (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by
  classical

  let W₁ : T.Y.Opens := W.ι ''ᵁ (ε.1 ⁻¹ᵁ (V c))
  have hW₁W : W₁ ≤ W := by simpa using W.ι.image_le_opensRange (ε.1 ⁻¹ᵁ (V c))
  let U : (pullback z f).Opens := U₁ ⊓ U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁)
  have hUU₁ : U ≤ U₁ := inf_le_left
  have hUU₀ : U ≤ U₀ := hUU₁.trans h₁
  have hηU' : η ∈ U := by
    refine ⟨hηU₁, ?_⟩
    show η ∈ (U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁) : Set _)
    rw [Scheme.Hom.coe_image]
    refine ⟨⟨η, hηU⟩, ?_, rfl⟩
    show τ₀.1.base ⟨η, hηU⟩ ∈ (W₁ : Set _)
    rw [hyτ, Scheme.Hom.coe_image]
    exact ⟨⟨T.y, hyW⟩, show ε.1.base ⟨T.y, hyW⟩ ∈ V c by rw [hεy]; exact hyV c, rfl⟩

  let t₁ : (U : Scheme.{u}) ⟶ T.Y := (pullback z f).homOfLE hUU₀ ≫ τ₀.1
  have hι_homOfLE : ∀ u : (U : Scheme.{u}), U₀.ι.base (((pullback z f).homOfLE hUU₀).base u) = u.1 := by
    intro u
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have ht₁W₁ : ∀ u : (U : Scheme.{u}), t₁.base u ∈ W₁ := by
    intro u
    obtain ⟨w, hw, hwu⟩ := (show u.1 ∈ (U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁) : Set _) from u.2.2)
    have hw' : w = ((pullback z f).homOfLE hUU₀).base u :=
      U₀.ι.isOpenEmbedding.injective (hwu.trans (hι_homOfLE u).symm)
    show τ₀.1.base (((pullback z f).homOfLE hUU₀).base u) ∈ W₁
    rw [← hw']; exact hw
  have hrange₁ : Set.range t₁.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW₁W (ht₁W₁ u)
  let t₂ : (U : Scheme.{u}) ⟶ (W : Scheme.{u}) := IsOpenImmersion.lift W.ι t₁ hrange₁
  have ht₂ : t₂ ≫ W.ι = t₁ := IsOpenImmersion.lift_fac _ _ _

  have ht₂V : ∀ u : (U : Scheme.{u}), (t₂ ≫ ε.1).base u ∈ V c := by
    intro u
    obtain ⟨w, hw, hwu⟩ := (show t₁.base u ∈ (W₁ : Set _) from ht₁W₁ u)
    have hw' : w = t₂.base u :=
      W.ι.isOpenEmbedding.injective (hwu.trans (by rw [← Scheme.Hom.comp_apply, ht₂]))
    rw [Scheme.Hom.comp_apply, ← hw']
    exact hw
  have hrange₂ : Set.range (t₂ ≫ ε.1).base ⊆ Set.range (V c).ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht₂V u
  let t₄ : (U : Scheme.{u}) ⟶ (V c : Scheme.{u}) := IsOpenImmersion.lift (V c).ι (t₂ ≫ ε.1) hrange₂
  have ht₄ : t₄ ≫ (V c).ι = t₂ ≫ ε.1 := IsOpenImmersion.lift_fac _ _ _

  have hUover : U.ι ≫ pullback.fst z f ≫ z = (pullback z f).homOfLE hUU₀ ≫ U₀.ι ≫ pullback.fst z f ≫ z := by
    rw [Scheme.homOfLE_ι_assoc]
  let a : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (U₀.ι ≫ pullback.fst z f ≫ z) :=
    ⟨(pullback z f).homOfLE hUU₀, hUover.symm⟩
  let b : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (W.ι ≫ T.f) :=
    ⟨t₂, by rw [← Category.assoc, ht₂, Category.assoc, τ₀.2, hUover]⟩
  let dd : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) ((V c).ι ≫ (D.C c).f) :=
    ⟨t₄, by rw [← Category.assoc, ht₄, Category.assoc, ε.2, ← Category.assoc, ht₂, Category.assoc, τ₀.2, hUover]⟩
  let τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f := NeronModelInfra.schemeHomOverComp dd (j c)
  have hba : NeronModelInfra.schemeHomOverComp b ⟨W.ι, rfl⟩ = NeronModelInfra.schemeHomOverComp a τ₀ :=
    Subtype.ext ht₂
  have hdb : NeronModelInfra.schemeHomOverComp dd ⟨(V c).ι, rfl⟩ = NeronModelInfra.schemeHomOverComp b ε :=
    Subtype.ext ht₄
  refine ⟨U, hηU', τ, ?_, ?_⟩
  ·
    haveI := hjopen c
    haveI := hε
    haveI := hv
    have ht₁def : t₁ = (pullback z f).homOfLE hUU₀ ≫ τ₀.1 := rfl
    obtain ⟨mW, hmW⟩ : ∃ m : pullback z (W.ι ≫ T.f) ⟶ pullback z T.f,
        m = pullback.map z (W.ι ≫ T.f) z T.f (𝟙 Z) W.ι (𝟙 _) (by simp) (by simp) := ⟨_, rfl⟩
    obtain ⟨mε, hmε⟩ : ∃ m : pullback z (W.ι ≫ T.f) ⟶ pullback z (D.C c).f,
        m = pullback.map z (W.ι ≫ T.f) z (D.C c).f (𝟙 Z) ε.1 (𝟙 _) (by simp)
          (by rw [Category.comp_id, ε.2]) := ⟨_, rfl⟩
    obtain ⟨mV, hmV⟩ : ∃ m : pullback z ((V c).ι ≫ (D.C c).f) ⟶ pullback z (D.C c).f,
        m = pullback.map z ((V c).ι ≫ (D.C c).f) z (D.C c).f (𝟙 Z) (V c).ι (𝟙 _) (by simp) (by simp) := ⟨_, rfl⟩
    obtain ⟨mj, hmj⟩ : ∃ m : pullback z ((V c).ι ≫ (D.C c).f) ⟶ pullback z f,
        m = pullback.map z ((V c).ι ≫ (D.C c).f) z f (𝟙 Z) (j c).1 (𝟙 _) (by simp)
          (by rw [Category.comp_id, (j c).2]) := ⟨_, rfl⟩
    haveI : IsOpenImmersion mW := by rw [hmW]; infer_instance
    haveI : IsOpenImmersion mε := by rw [hmε]; infer_instance
    haveI : IsOpenImmersion mV := by rw [hmV]; infer_instance
    haveI : IsOpenImmersion mj := by rw [hmj]; infer_instance

    obtain ⟨M₁, hM₁⟩ : ∃ m : (U : Scheme.{u}) ⟶ pullback z (W.ι ≫ T.f),
        m = pullback.lift (U.ι ≫ pullback.fst z f) t₂ (by rw [Category.assoc]; exact b.2.symm) := ⟨_, rfl⟩
    have hM₁v : M₁ ≫ mW = (pullback z f).homOfLE hUU₁ ≫ ((pullback z f).homOfLE h₁ ≫ v) := by
      rw [hM₁, hmW]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, hv₁, Scheme.homOfLE_ι_assoc]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hv₂, Scheme.homOfLE_homOfLE_assoc,
          ht₂, ht₁def]
    haveI : IsOpenImmersion (M₁ ≫ mW) := by rw [hM₁v]; infer_instance
    haveI : IsOpenImmersion M₁ := IsOpenImmersion.of_comp M₁ mW

    obtain ⟨M₃, hM₃⟩ : ∃ m : (U : Scheme.{u}) ⟶ pullback z ((V c).ι ≫ (D.C c).f),
        m = pullback.lift (U.ι ≫ pullback.fst z f) t₄ (by rw [Category.assoc]; exact dd.2.symm) := ⟨_, rfl⟩
    have hM₃M₁ : M₃ ≫ mV = M₁ ≫ mε := by
      rw [hM₃, hmV, hM₁, hmε]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ht₄]
    haveI : IsOpenImmersion (M₃ ≫ mV) := by rw [hM₃M₁]; infer_instance
    haveI : IsOpenImmersion M₃ := IsOpenImmersion.of_comp M₃ mV

    have hL : pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
        ((Category.assoc _ _ _).trans τ.2.symm) = M₃ ≫ mj := by
      rw [hM₃, hmj]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        rfl
    rw [hL]
    infer_instance
  ·
    have hF := fun {A B C : Scheme.{u}} (fa : A ⟶ Spec (CommRingCat.of R)) (fb : B ⟶ Spec (CommRingCat.of R))
        (fc : C ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver fb fa) (ψ : SchemeHomOver fa fc) =>
      congrArg Subtype.val (NeronModelInfra.genericFibreRestrict_schemeHomOverComp R K fa fb fc φ ψ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at hF
    have S6 := hτ₀
    rw [NeronModelInfra.schemeHomOverComp_coe] at S6
    have ha1 : a.1 = (pullback z f).homOfLE hUU₀ := rfl
    have S7 : (genericFibreRestrict R K (U₀.ι ≫ pullback.fst z f ≫ z) (U.ι ≫ pullback.fst z f ≫ z) a).1 ≫
        pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
          (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
          (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
      apply pullback.hom_ext
      · simp only [NeronModelInfra.genericFibreRestrict, ha1, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, Scheme.homOfLE_ι]
      · simp only [NeronModelInfra.genericFibreRestrict, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
    rw [NeronModelInfra.schemeHomOverComp_coe]
    change (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp dd (j c))).1 ≫ e.1 = _
    rw [reassoc_of% (hF _ _ _ dd (j c)), hjchart c, ← reassoc_of% (hF _ _ _ dd ⟨(V c).ι, rfl⟩), hdb,
      reassoc_of% (hF _ _ _ b ε), hεchart, ← reassoc_of% (hF _ _ _ b ⟨W.ι, rfl⟩), hba,
      reassoc_of% (hF _ _ _ a τ₀), S6, reassoc_of% S7]

end S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep (solution)
