-- Prove2me | solution 1 for NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/43df3e44-ec51-5834-8969-9308e6e5a287

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

import Theorems.Thm_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints
import Theorems.Thm_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
import Theorems.Thm_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
import Theorems.Thm_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
import Theorems.Thm_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
import Theorems.Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        letI := gK.sectionsAlgebra U'; letI := gK.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d (gK.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
          gK.topToSections d U' ω' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          gK.topToSections d U'' ω'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F d ω'))
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
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base) :
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
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
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
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
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1)  := by
  classical
  have hL : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
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
    intro Z z _ _ uK η hη hmax

    let ΦK : SchemeHomOver (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K)) gK :=
      LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f, pullback.condition.symm⟩) e)

    obtain ⟨i, U₀, hηU, τ₀, hτ₀⟩ :=
      NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints K M (fun i => (hM i).2.2.1) hpts
        (pullback.fst z f ≫ z) ΦK η hη hmax
    haveI : Smooth (M.str i) := (hM i).1
    haveI : LocallyOfFiniteType (M.str i) := (hM i).2.2.1
    haveI : QuasiCompact (M.str i) := (hM i).2.2.2

    have hy' : (M.str i).base (τ₀.1.base ⟨η, hηU⟩) = IsLocalRing.closedPoint R := by
      have h2 := congrArg (fun φ => φ.base ⟨η, hηU⟩) τ₀.2
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
      rw [h2]; exact hη

    obtain ⟨-, huniq, -⟩ :=
      NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens (M.str i)
    obtain ⟨ξ, ⟨⟨hξ, hξmax⟩, hξgen⟩, -⟩ := huniq _ hy'
    obtain ⟨hdom, hdvr, alg, halg, algK, hst, b, U, hU, algU, hstU, hx, ωU, hωU, a, ha, ha0⟩ :=
      NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes K gK d ω hωframe
        (M.str i) (M.chart i) ξ hξ hξmax
    let T : ComponentReading R K gK d ω :=
      ⟨M.X i, M.str i, inferInstance, inferInstance, M.chart i, inferInstance, ξ, hξ, hξmax,
        hdom, hdvr, alg, halg, algK, hst, b, U, hU, algU, hstU, hx, ωU, hωU, a, ha, ha0⟩

    let v : (U₀ : Scheme.{u}) ⟶ pullback z T.f :=
      pullback.lift (U₀.ι ≫ pullback.fst z f) τ₀.1 ((Category.assoc _ _ _).trans τ₀.2.symm)
    have hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f := pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd z T.f = τ₀.1 := pullback.lift_snd _ _ _

    obtain ⟨hdomO, hdomO', hfrac⟩ :=
      NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    obtain ⟨hn, hfs⟩ :=
      NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul K LXK d ω hωframe hleft D hD X f e V j hyV hVK hjopen hjchart hcover
        Z z uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ hξgen
    exact NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal K LXK d ω D hD X f e V j hyV hVK hjopen hjchart hcover
      Z z uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ hξgen hn hdomO hdomO' hfrac hfs
  refine ⟨hL, ?_⟩

  intro Z z _ _ uK η hη hmax
  obtain ⟨U, hU, τ, h1, h2⟩ := hL Z z uK η hη hmax
  refine ⟨U, hU, τ, h1, ?_⟩
  rw [h2, hcomm.mul_comm]

end S_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
end P2MW
export P2MW.S_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative (solution)
