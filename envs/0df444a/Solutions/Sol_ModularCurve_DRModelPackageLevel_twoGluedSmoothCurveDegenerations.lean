-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.twoGluedSmoothCurveDegenerations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e4a3265b-f0e7-5e59-90ea-9613a2b6920c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_twoGluedSmoothCurveDegenerations
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q))), ¬ Smooth (pullback.snd (DRLevel.toBase N₀ q) s) →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (DRLevel.toBase N₀ q) s)) (i₂ : SchemeHomOver c₂ (pullback.snd (DRLevel.toBase N₀ q) s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (DRLevel.toBase N₀ q) s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s))
            (((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) =
          ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s)) \
            connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) s ⁻¹ᵁ 𝔓.smoothLocus : (pullback (DRLevel.toBase N₀ q) s).Opens) : Set ↥(pullback (DRLevel.toBase N₀ q) s))
              (((sectionFibrePoint 𝔓.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (DRLevel.toBase N₀ q) s).Opens, (W₁ : Set ↥(pullback (DRLevel.toBase N₀ q) s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (DRLevel.toBase N₀ q) s).Opens, (W₂ : Set ↥(pullback (DRLevel.toBase N₀ q) s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  intro k _ _ s hns
  classical
  haveI := 𝔓.flat
  haveI := 𝔓.lfp
  haveI := 𝔓.isProper
  obtain ⟨toκ, hchar, rfl⟩ := 𝔓.exists_ringHom_charP_of_not_smooth_fibre N₀ q hqN s hns
  haveI := hchar

  haveI hp0 : IsProper (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 toκ
  haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 toκ
  haveI hgi0 : GeometricallyIntegral (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI := 𝔓.comp_isClosedImmersion k toκ 0
  haveI := 𝔓.comp_isClosedImmersion k toκ 1
  haveI hred := 𝔓.fibre_reduced k toκ
  haveI hcr := 𝔓.crossing_reduced k toκ
  haveI : Finite ↥(pullback (𝔓.comp k toκ 0) (𝔓.comp k toκ 1)) := 𝔓.finite_crossings toκ

  let i₁ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp k toκ 0, 𝔓.comp_over k toκ 0⟩
  let i₂ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp k toκ 1, 𝔓.comp_over k toκ 1⟩
  have hsec : (sectionFibrePoint 𝔓.εinf (Spec.map (CommRingCat.ofHom toκ))).1 = DRLevel.sectionFibre 𝔓.εinf toκ := rfl
  set p := ((sectionFibrePoint 𝔓.εinf (Spec.map (CommRingCat.ofHom toκ))).1).base (IsLocalRing.closedPoint k) with hpdef
  have hp1 : p ∈ Set.range (𝔓.comp k toκ 0).base := 𝔓.εinf_mem_comp0 k toκ ⟨IsLocalRing.closedPoint k, by rw [hpdef, hsec]⟩
  have hpU : p ∈ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).Opens) : Set _) := by
    show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base p ∈ (𝔓.smoothLocus : Set _)
    apply 𝔓.εinf_mem_smoothLocus
    refine ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint k), ?_⟩
    rw [hpdef, hsec, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst]

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
  obtain ⟨hU, hU₁, hU₂, hW₁, hW₂⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (DRLevel.toBase N₀ q) 𝔓.smoothLocus 𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      i₁ i₂ (𝔓.comp_jointly_surjective k toκ) hne₁ hne₂ p hp1 hpU

  have hn : 0 < Nat.card ↥(pullback (𝔓.comp k toκ 0) (𝔓.comp k toκ 1)) := by
    haveI : Nonempty ↥(pullback (𝔓.comp k toκ 0) (𝔓.comp k toκ 1)) := by
      obtain ⟨P, hP⟩ := ModularCurve.ssPlaces_nonempty q N₀ hqN k
      exact ⟨(𝔓.nodeEquiv k toκ).symm ⟨P, hP⟩⟩
    exact Nat.card_pos

  have hp2 : p ∉ Set.range (𝔓.comp k toκ 1).base := by
    intro h2
    have hpc : p ∈ Set.range (pullback.fst (𝔓.comp k toκ 0) (𝔓.comp k toκ 1) ≫ 𝔓.comp k toκ 0).base := by
      obtain ⟨a, ha⟩ := hp1
      obtain ⟨b, hb⟩ := h2
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz1, ha]⟩
    rw [hU] at hpU
    exact hpU hpc
  refine ⟨DRLevel.fibre0 (N₀ := N₀) toκ, DRLevel.fibre0 (N₀ := N₀) toκ,
    pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)),
    pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)),
    hp0, hs0, hgi0, hp0, hs0, hgi0, i₁, i₂, inferInstance, inferInstance, Nat.card ↥(pullback (𝔓.comp k toκ 0) (𝔓.comp k toκ 1)),
    𝔓.comp_jointly_surjective k toκ, hcr, rfl, hn, ⟨hp1, hp2⟩, hU, hU₁, hU₂, hW₁, hW₂⟩

end S_ModularCurve_DRModelPackageLevel_twoGluedSmoothCurveDegenerations
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_twoGluedSmoothCurveDegenerations (solution)
