-- Prove2me | solution 1 for NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a73e4c19-b82c-5156-8a81-2323c077b619

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
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
import Theorems.Thm_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift.NeronModelInfra GoodReductionJacobian"

universe u

namespace NeronModelInfra
p2m_export "NeronModelInfra" "specGenericFibreInclusion SchemeHomOver genericFibreRestrict schemeHomOverComp schemeHomOverComp_coe ComponentReading range_specGenericFibreInclusion_eq_basicOpen"
namespace L0
p2m_open "NeronModelInfra"

theorem isOpenImmersion_opensRange_ι_comp_translate
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    [IsOpenImmersion (specGenericFibreInclusion R K)]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (CommRingCat.of R))
    (eY : SchemeHomOver (pullback.snd fY (specGenericFibreInclusion R K)) gK) [IsOpenImmersion eY.1]
    (U₀ : (pullback z f).Opens) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) fY)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K fY (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) eY).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z fY) (hv₁ : v ≫ pullback.fst z fY = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z fY = τ₀.1) :
    IsOpenImmersion
      ((pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)).opensRange.ι ≫ v) := by

  have hq : v ≫ (pullback.fst z fY ≫ z) = (U₀.ι ≫ pullback.fst z f ≫ z) := by
    simp only [← Category.assoc, hv₁]

  let mapU : pullback (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) :=
    pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let w : pullback (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) :=
    pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) v (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hq])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hmapU : IsOpenImmersion mapU :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion U₀.ι)
      (inferInstance : IsOpenImmersion (𝟙 _)) rfl (Category.id_comp _).symm

  let β : pullback (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f (specGenericFibreInclusion R K)) :=
    pullback.lift
      (pullback.lift (pullback.fst (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ pullback.fst z f) (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift (pullback.fst (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ pullback.snd z f) (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
      (by rw [pullback.lift_snd, pullback.lift_snd])
  haveI hβ : IsIso β := AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd z f (specGenericFibreInclusion R K)
  let βY : pullback (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ⟶ pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY (specGenericFibreInclusion R K)) :=
    pullback.lift
      (pullback.lift (pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ≫ pullback.fst z fY) (pullback.snd (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift (pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ≫ pullback.snd z fY) (pullback.snd (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc, ← pullback.condition (f := z) (g := fY)]; exact pullback.condition))
      (by rw [pullback.lift_snd, pullback.lift_snd])
  haveI hβY : IsIso βY := AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd z fY (specGenericFibreInclusion R K)

  let mapE : pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f (specGenericFibreInclusion R K)) ⟶ pullback (pullback.snd z (specGenericFibreInclusion R K)) gK :=
    pullback.map (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f (specGenericFibreInclusion R K)) (pullback.snd z (specGenericFibreInclusion R K)) gK (𝟙 _) e.1 (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans e.2.symm)
  let mapEY : pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY (specGenericFibreInclusion R K)) ⟶ pullback (pullback.snd z (specGenericFibreInclusion R K)) gK :=
    pullback.map (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY (specGenericFibreInclusion R K)) (pullback.snd z (specGenericFibreInclusion R K)) gK (𝟙 _) eY.1 (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans eY.2.symm)
  have hmapEY : IsOpenImmersion mapEY :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion (𝟙 _))
      (inferInstance : IsOpenImmersion eY.1) (Category.id_comp _).symm eY.2.symm

  obtain ⟨σ, hσ₁, hσ₂⟩ := LXK.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul (pullback.snd z (specGenericFibreInclusion R K)) uK

  have key : w ≫ βY ≫ mapEY = mapU ≫ β ≫ mapE ≫ σ.hom := by
    apply pullback.hom_ext
    ·
      simp only [Category.assoc, hσ₁]
      simp only [mapEY, mapE, pullback.lift_fst, Category.comp_id, βY, β]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, w, mapU]
        simp only [← Category.assoc, pullback.lift_fst]
        simp only [Category.assoc, hv₁]
      · simp only [Category.assoc, pullback.lift_snd, w, mapU]
    ·
      have hψ : (β ≫ mapE) ≫ pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ (pullback.snd z (specGenericFibreInclusion R K)) = pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) := by
        simp only [Category.assoc, mapE, β, pullback.lift_fst_assoc, Category.id_comp, pullback.lift_snd]
      have nat := congrArg Subtype.val
        (LXK.mul_natural (pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ (pullback.snd z (specGenericFibreInclusion R K))) (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K)) (β ≫ mapE) hψ
          ⟨pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ uK.1, by rw [Category.assoc, uK.2]⟩
          ⟨pullback.snd (pullback.snd z (specGenericFibreInclusion R K)) gK, pullback.condition.symm⟩)
      simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nat
      have hA : GoodReductionJacobian.schemeHomOverComp (β ≫ mapE) hψ
            ⟨pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ uK.1, by rw [Category.assoc, uK.2]⟩ =
          NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
          genericFibreRestrict, Category.assoc, mapE, β, pullback.lift_fst_assoc, Category.id_comp]
        all_goals rfl
      have hB : GoodReductionJacobian.schemeHomOverComp (β ≫ mapE) hψ
            ⟨pullback.snd (pullback.snd z (specGenericFibreInclusion R K)) gK, pullback.condition.symm⟩ =
          NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f, pullback.condition.symm⟩) e := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
          genericFibreRestrict, Category.assoc, mapE, β, pullback.lift_snd_assoc, pullback.lift_snd]
        all_goals rfl
      rw [hA, hB] at nat

      have eL : (w ≫ βY ≫ mapEY) ≫ pullback.snd (pullback.snd z (specGenericFibreInclusion R K)) gK =
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K fY (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) eY).1 := by
        simp only [NeronModelInfra.schemeHomOverComp_coe, genericFibreRestrict, Category.assoc, mapEY,
          pullback.lift_snd_assoc, pullback.lift_snd]
        simp only [← Category.assoc]
        congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, βY, w, hv₂]
          all_goals rfl
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, βY, w, Category.comp_id]
          all_goals rfl
      rw [eL, hτ₀]
      simp only [Category.assoc, hσ₂]
      rw [← nat]
      simp only [Category.assoc, mapU]
      all_goals rfl

  haveI : IsOpenImmersion (mapU ≫ β ≫ mapE ≫ σ.hom) := inferInstance
  have hwc : IsOpenImmersion (w ≫ βY ≫ mapEY) := by rw [key]; infer_instance
  haveI : IsOpenImmersion (βY ≫ mapEY) := inferInstance
  have hw : IsOpenImmersion w := IsOpenImmersion.of_comp w (βY ≫ mapEY)

  have h4 : pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ v = w ≫ pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) := by
    simp only [w, pullback.lift_fst]
  haveI h5 : IsOpenImmersion (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ v) := by rw [h4]; infer_instance
  have h6 : (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)).opensRange.ι ≫ v =
      (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)).isoOpensRange.inv ≫ pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ v := by
    rw [Scheme.Hom.isoOpensRange_inv_comp_assoc]
  rw [h6]
  infer_instance

end NeronModelInfra.L0

namespace NeronModelInfra
p2m_export "NeronModelInfra" "specGenericFibreInclusion SchemeHomOver genericFibreRestrict schemeHomOverComp schemeHomOverComp_coe ComponentReading range_specGenericFibreInclusion_eq_basicOpen"
namespace L0
p2m_open "NeronModelInfra"

theorem exists_mem_opensRange_fst_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) [Flat s] (x : S) :
    ∃ x' : S, x' ∈ (pullback.fst s (specGenericFibreInclusion R K)).opensRange ∧ x' ⤳ x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let ξ : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
  have hξ : (ξ : Spec (CommRingCat.of R)) ⤳ s.base x :=
    (PrimeSpectrum.le_iff_specializes ξ (s.base x)).mp bot_le
  obtain ⟨x', hx', hx'ξ⟩ := Flat.generalizingMap s hξ
  refine ⟨x', ?_, hx'⟩
  rw [AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst]
  show s.base x' ∈ Set.range (specGenericFibreInclusion R K).base
  rw [range_specGenericFibreInclusion_eq_basicOpen R K hϖ, hx'ξ]
  show ξ ∈ PrimeSpectrum.basicOpen ϖ
  rw [PrimeSpectrum.mem_basicOpen]
  show ϖ ∉ (⊥ : Ideal R)
  rw [Ideal.mem_bot]
  exact hϖ.ne_zero

end NeronModelInfra.L0

open NeronModelInfra.L0 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
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
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1) :
    ∃ (_ : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
      (_ : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))),
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := by
  haveI hTs : Smooth T.f := T.smooth
  haveI hTe : IsOpenImmersion T.e.1 := T.isOpenImmersion

  have hD1 : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (U₀.ι ≫ pullback.fst z f ≫ z) ⟨η, hηU⟩).1
  have hD2 : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst z T.f ≫ z) (v.base ⟨η, hηU⟩)).1
  refine ⟨hD1, hD2, ?_⟩

  obtain ⟨x', hx'U, hx'η⟩ :=
    exists_mem_opensRange_fst_specializes K (U₀.ι ≫ pullback.fst z f ≫ z) ⟨η, hηU⟩

  haveI := isOpenImmersion_opensRange_ι_comp_translate K LXK X f e Z z uK T.Y T.f T.e U₀ τ₀ hτ₀ v hv₁ hv₂
  exact AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict v ⟨η, hηU⟩
    (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)).opensRange ⟨x', hx'U, hx'η⟩

end S_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
end P2MW
export P2MW.S_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift (solution)
