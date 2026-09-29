-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/881e88f5-1e44-5ffd-bdca-74f5c1127ac2

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
import Theorems.Thm_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
import Theorems.Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

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
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩)
    (hn : ∃ c : D.ι, T.n = (D.C c).n)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
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

  obtain ⟨hyτ, U₁, hηU₁, h₁, hv⟩ :=
    AlgebraicGeometry.Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk z f T.f η hη hmax T.y T.hy U₀ hηU v hv₁ (by rw [hv₂]; exact hgen)
      hdom hdom' hfrac hfs

  obtain ⟨c, W, hyW, ε, hε, hεy, hεchart⟩ := hD.2 T hn

  exact NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep K LXK d ω D hD X f e V j hyV hVK hjopen hjchart hcover Z z uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    U₁ hηU₁ h₁ hv (by rw [← hv₂]; exact hyτ) c W hyW ε hε hεy hεchart

end S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal (solution)
