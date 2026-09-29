-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1c8c3569-820a-5453-9362-492278efe5ea

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R p →+* κ)
    (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) :
    y ∈ (pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus) ↔
      ¬ (y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∈ Set.range (𝔓.comp κ toκ 1).base) := by
  classical
  haveI := 𝔓.flat
  haveI := 𝔓.lfp
  haveI : IsProper (DRLevel.toBase N₀ p) := 𝔓.isProper

  haveI hp0 : IsProper (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 _
  haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 _
  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 _
  haveI hgi0 : GeometricallyIntegral (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  have hred := 𝔓.fibre_reduced κ toκ
  let i₁ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp κ toκ 0, 𝔓.comp_over κ toκ 0⟩
  let i₂ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp κ toκ 1, 𝔓.comp_over κ toκ 1⟩

  set pε := (DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ) with hpεdef
  have hpε1 : pε ∈ Set.range (𝔓.comp κ toκ 0).base := 𝔓.εinf_mem_comp0 _ _ ⟨IsLocalRing.closedPoint _, by rw [hpεdef]⟩
  have hpεU : pε ∈ ((pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))).Opens) : Set _) := by
    show (pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))).base pε ∈ (𝔓.smoothLocus : Set _)
    apply 𝔓.εinf_mem_smoothLocus
    refine ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint _), ?_⟩
    rw [hpεdef, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst]
  haveI : Smooth (𝔓.smoothLocus.ι ≫ DRLevel.toBase N₀ p) := by
    haveI := 𝔓.smoothLocus_relDim
    infer_instance

  let wb : ↥(DRLevel.fibre (N₀ := N₀) toκ) → ↥(DRLevel.fibre (N₀ := N₀) toκ) := (DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base
  have hr1 : Set.range (𝔓.comp κ toκ 1).base = wb '' Set.range (𝔓.comp κ toκ 0).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp_w κ toκ]; rfl : (𝔓.comp κ toκ 1).base a = wb ((𝔓.comp κ toκ 0).base a)))
  have hr0 : Set.range (𝔓.comp κ toκ 0).base = wb '' Set.range (𝔓.comp κ toκ 1).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp1_fibreMap_w toκ]; rfl : (𝔓.comp κ toκ 0).base a = wb ((𝔓.comp κ toκ 1).base a)))
  have hne₁ : ¬ Set.range (𝔓.comp κ toκ 0).base ⊆ Set.range (𝔓.comp κ toκ 1).base := fun h =>
    𝔓.range_comp_ne κ toκ (Set.Subset.antisymm h (by rw [hr1]; nth_rw 2 [hr0]; exact Set.image_mono h))
  have hne₂ : ¬ Set.range (𝔓.comp κ toκ 1).base ⊆ Set.range (𝔓.comp κ toκ 0).base := fun h =>
    𝔓.range_comp_ne κ toκ (Set.Subset.antisymm (by rw [hr0]; nth_rw 2 [hr1]; exact Set.image_mono h) h)

  obtain ⟨hU, -, -, -, -⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (DRLevel.toBase N₀ p) 𝔓.smoothLocus 𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)))
      i₁ i₂ (𝔓.comp_jointly_surjective κ toκ) hne₁ hne₂ pε hpε1 hpεU

  have hiff : y ∈ Set.range (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base ↔
      (y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∈ Set.range (𝔓.comp κ toκ 1).base) := by
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨(pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base z, (Scheme.Hom.comp_apply _ _ _).symm⟩,
        ⟨(pullback.snd (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)).base z, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, ha]⟩
  change y ∈ ((pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (pullback (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))).Opens) : Set _) ↔ _
  rw [hU, Set.mem_compl_iff, hiff]

end S_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter (solution)
