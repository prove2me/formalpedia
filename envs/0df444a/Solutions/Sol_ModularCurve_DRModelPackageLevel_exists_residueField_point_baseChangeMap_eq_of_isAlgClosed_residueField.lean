-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0ec5dd2b-fb74-5cf0-92f4-36751b96a75e

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace HratLevel

p2m_open "NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian CategoryTheory.MonoidalCategory"

private theorem preimage_smoothLocus_eq_compl_range
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (toκ : DRLevel.R q →+* k) :
    ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
        (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ)) =
      (Set.range (pullback.fst (𝔓.comp k toκ 0) (𝔓.comp k toκ 1) ≫ 𝔓.comp k toκ 0).base)ᶜ := by
  classical
  haveI := 𝔓.flat
  haveI := 𝔓.lfp
  haveI := 𝔓.isProper
  haveI hp0 : IsProper (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 toκ
  haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 toκ
  haveI hgi0 : GeometricallyIntegral (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI := 𝔓.comp_isClosedImmersion k toκ 0
  haveI := 𝔓.comp_isClosedImmersion k toκ 1
  haveI hred := 𝔓.fibre_reduced k toκ
  let i₁ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp k toκ 0, 𝔓.comp_over k toκ 0⟩
  let i₂ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp k toκ 1, 𝔓.comp_over k toκ 1⟩
  set p := (DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint k) with hpdef
  have hp1 : p ∈ Set.range (𝔓.comp k toκ 0).base := 𝔓.εinf_mem_comp0 k toκ ⟨IsLocalRing.closedPoint k, by rw [hpdef]⟩
  have hpU : p ∈ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).Opens) : Set _) := by
    show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base p ∈ (𝔓.smoothLocus : Set _)
    apply 𝔓.εinf_mem_smoothLocus
    refine ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint k), ?_⟩
    rw [hpdef, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst]
  haveI : Smooth (𝔓.smoothLocus.ι ≫ DRLevel.toBase N₀ q) := by
    haveI := 𝔓.smoothLocus_relDim
    infer_instance
  let wb : ↥(DRLevel.fibre (N₀ := N₀) toκ) → ↥(DRLevel.fibre (N₀ := N₀) toκ) := (DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base
  have hr1 : Set.range (𝔓.comp k toκ 1).base = wb '' Set.range (𝔓.comp k toκ 0).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp_w k toκ]; rfl : (𝔓.comp k toκ 1).base a = wb ((𝔓.comp k toκ 0).base a)))
  have hr0 : Set.range (𝔓.comp k toκ 0).base = wb '' Set.range (𝔓.comp k toκ 1).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp1_fibreMap_w toκ]; rfl : (𝔓.comp k toκ 0).base a = wb ((𝔓.comp k toκ 1).base a)))
  have hne₁ : ¬ Set.range (𝔓.comp k toκ 0).base ⊆ Set.range (𝔓.comp k toκ 1).base := fun h =>
    𝔓.range_comp_ne k toκ (Set.Subset.antisymm h (by rw [hr1]; nth_rw 2 [hr0]; exact Set.image_mono h))
  have hne₂ : ¬ Set.range (𝔓.comp k toκ 1).base ⊆ Set.range (𝔓.comp k toκ 0).base := fun h =>
    𝔓.range_comp_ne k toκ (Set.Subset.antisymm (by rw [hr0]; nth_rw 2 [hr1]; exact Set.image_mono h) h)
  exact (AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (DRLevel.toBase N₀ q) 𝔓.smoothLocus 𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      i₁ i₂ (𝔓.comp_jointly_surjective k toκ) hne₁ hne₂ p hp1 hpU).1

end HratLevel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [IsAlgClosed (IsLocalRing.ResidueField O)]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) :
    ∀ x : ↥(pullback (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRLevel.bcMap ρO toκ).base ((pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base x) =
          (DRLevel.bcMap ρO (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) := by
  intro x
  classical

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  let ι : IsLocalRing.ResidueField O →+* κ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ hker
  have hι : ι.comp (IsLocalRing.residue O) = toκ := RingHom.ext fun a => rfl
  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.mem_span_singleton_self _
  haveI hchar : CharP (IsLocalRing.ResidueField O) p := ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero Fact.out hp0)

  let g : DRLevel.fibre (N₀ := N₀) (toκ.comp ρO) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ι)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hι])
  have hgbc : g ≫ DRLevel.bcMap ρO (IsLocalRing.residue O) = DRLevel.bcMap (N₀ := N₀) ρO toκ := by
    apply pullback.hom_ext
    · simp only [g, DRLevel.bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [g, DRLevel.bcMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hι]
  have hgfst : g ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue O).comp ρO))) =
      pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    simp only [g, pullback.map, pullback.lift_fst, Category.comp_id]

  let x' : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)) :=
    (pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base x
  let y₀ : ↥(DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO)) := g.base x'

  have hx'U : x' ∉ ((pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) ⁻¹ᵁ 𝔓.smoothLocus :
      (DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)).Opens) : Set _) := by
    rw [HratLevel.preimage_smoothLocus_eq_compl_range N₀ p hpN₀ 𝔓 κ (toκ.comp ρO), Set.mem_compl_iff, not_not]
    exact ⟨x, rfl⟩
  have hy₀U : y₀ ∉ ((pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue O).comp ρO))) ⁻¹ᵁ
      𝔓.smoothLocus : (DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO)).Opens) : Set _) := by
    intro h
    apply hx'U
    show (pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base x' ∈ (𝔓.smoothLocus : Set _)
    rw [← hgfst, Scheme.Hom.comp_apply]
    exact h
  have hy₀c : y₀ ∈ Set.range (pullback.fst (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0)
      (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 1) ≫
      𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0).base := by
    have h := HratLevel.preimage_smoothLocus_eq_compl_range N₀ p hpN₀ 𝔓 (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO)
    by_contra hc
    exact hy₀U (by rw [h]; exact hc)
  obtain ⟨m, hm⟩ := hy₀c

  obtain ⟨⟨hcl, -⟩, -⟩ := 𝔓.node_pin (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) m
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton (IsLocalRing.ResidueField O)
    (𝔓.Mfib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO)).toBase _ (mem_closedPoints_iff.mp hcl)
  have hinv : (𝔓.efib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO)).base
      ((inv (𝔓.efib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO))).base
        ((pullback.fst (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0)
          (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 1)).base m)) =
      (pullback.fst (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0)
        (𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 1)).base m := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨z.left ≫ 𝔓.efib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) ≫
    𝔓.comp (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0, ?_, ?_⟩
  ·
    have e2 := 𝔓.comp_over (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO) 0
    have e3 := 𝔓.hefib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO)
    have e4 : z.left ≫ (𝔓.Mfib (IsLocalRing.ResidueField O) ((IsLocalRing.residue O).comp ρO)).toBase = 𝟙 _ := by
      simpa only [Over.mk_left, Over.mk_hom] using Over.w z
    simp only [Category.assoc]
    erw [e2, e3, e4]
    rfl
  ·
    show (DRLevel.bcMap ρO toκ).base x' = _
    rw [← hgbc, Scheme.Hom.comp_apply]
    show (DRLevel.bcMap ρO (IsLocalRing.residue O)).base y₀ = _
    simp only [Scheme.Hom.comp_apply]
    rw [← hm, Scheme.Hom.comp_apply, ← hinv, ← hz]

end S_ModularCurve_DRModelPackageLevel_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField (solution)
