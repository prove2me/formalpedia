-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/09cd3a7a-3021-5fa7-8a2a-5c7d7602b367

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst"
p2m_attr_erase "simp" "ModularCurve.DRLevel.sectionFibre_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

noncomputable section

private theorem g2L_comp_base_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) := by
  rw [Scheme.Hom.comp_base]; rfl

private theorem g2L_range_comp_eq {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  ext z
  simp only [Set.mem_range, Set.mem_image, g2L_comp_base_apply]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨f.base x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩

private theorem g2L_range_subset_of_mem {C Z : Scheme} [IrreducibleSpace C] (i : C ⟶ Z) (S : Set Z) (hS : IsClosed S)
    (h : i.base (genericPoint C) ∈ S) : Set.range i.base ⊆ S := by
  have h1 : Set.range ⇑i.base = ⇑i.base '' closure {genericPoint C} := by
    rw [genericPoint_closure, Set.image_univ]
  rw [h1]
  refine (image_closure_subset_closure_image i.base.hom.continuous).trans ?_
  rw [Set.image_singleton]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hS

private theorem g2L_isDVR (q : ℕ) [Fact q.Prime] : IsDiscreteValuationRing (DRLevel.R q) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

attribute [local instance] g2L_isDVR

private theorem g2L_hϖ (q : ℕ) [Fact q.Prime] :
    IsLocalRing.maximalIdeal (DRLevel.R q) = Ideal.span {((q : ℕ) : DRLevel.R q)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out)

section Engine
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

private theorem g2L_wκ_invol :
    DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ ≫ DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [DRLevel.fibreMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [𝔓.w_invol, Category.comp_id]
  · simp only [DRLevel.fibreMap, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

private theorem g2L_comp_one_wκ : 𝔓.comp κ toκ 1 ≫ DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ = 𝔓.comp κ toκ 0 := by
  rw [← 𝔓.comp_w κ toκ, Category.assoc, g2L_wκ_invol, Category.comp_id]

private theorem g2L_range_zero_not_subset :
    ¬ (Set.range (𝔓.comp κ toκ 0).base ⊆ Set.range (𝔓.comp κ toκ 1).base) := by
  intro h
  apply 𝔓.range_comp_ne κ toκ
  refine h.antisymm ?_
  have h1 := Set.image_mono (f := ⇑(DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base) h
  rwa [← g2L_range_comp_eq, ← g2L_range_comp_eq, 𝔓.comp_w, g2L_comp_one_wκ] at h1

private theorem g2L_range_one_not_subset :
    ¬ (Set.range (𝔓.comp κ toκ 1).base ⊆ Set.range (𝔓.comp κ toκ 0).base) := by
  intro h
  apply 𝔓.range_comp_ne κ toκ
  refine Set.Subset.antisymm ?_ h
  have h1 := Set.image_mono (f := ⇑(DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base) h
  rwa [← g2L_range_comp_eq, ← g2L_range_comp_eq, 𝔓.comp_w, g2L_comp_one_wκ] at h1

variable [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]

private theorem g2L_c0_notMem :
    (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range (𝔓.comp κ toκ 1).base := by
  intro h
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  exact g2L_range_zero_not_subset N₀ q hqN 𝔓 κ toκ
    (g2L_range_subset_of_mem _ _ (𝔓.comp κ toκ 1).isClosedEmbedding.isClosed_range h)

private theorem g2L_c1_notMem :
    (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range (𝔓.comp κ toκ 0).base := by
  intro h
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  exact g2L_range_one_not_subset N₀ q hqN 𝔓 κ toκ
    (g2L_range_subset_of_mem _ _ (𝔓.comp κ toκ 0).isClosedEmbedding.isClosed_range h)

private theorem g2L_eq_of_specializes_c0 (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔓.comp κ toκ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔓.comp κ toκ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (g2L_c0_notMem N₀ q hqN 𝔓 κ toκ)

private theorem g2L_eq_of_specializes_c1 (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔓.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔓.comp κ toκ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (g2L_c1_notMem N₀ q hqN 𝔓 κ toκ)
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔓.comp κ toκ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
  (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)

private theorem g2L_toκ_maximalIdeal (a : DRLevel.R q) (ha : a ∈ IsLocalRing.maximalIdeal (DRLevel.R q)) : toκ a = 0 := by
  rw [g2L_hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

private def g2L_ι : IsLocalRing.ResidueField (DRLevel.R q) →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (DRLevel.R q)) toκ (g2L_toκ_maximalIdeal q κ toκ)

private theorem g2L_ι_comp_residue : (g2L_ι q κ toκ).comp (IsLocalRing.residue (DRLevel.R q)) = toκ :=
  RingHom.ext fun _ => rfl

private def g2L_bc {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) : DRLevel.fibre (N₀ := N₀) ρB ⟶ DRLevel.fibre (N₀ := N₀) ρA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ])

private theorem g2L_bc_fst {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    g2L_bc N₀ q ρA ρB φ hφ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [g2L_bc, pullback.lift_fst, Category.comp_id]

private theorem g2L_bc_snd {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    g2L_bc N₀ q ρA ρB φ hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [g2L_bc, pullback.lift_snd]

private theorem g2L_isPullback_bc {A B : Type} [CommRing A] [CommRing B] (ρA : DRLevel.R q →+* A) (ρB : DRLevel.R q →+* B)
    (φ : A →+* B) (hφ : φ.comp ρA = ρB) :
    IsPullback (g2L_bc N₀ q ρA ρB φ hφ)
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρB)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ρA) = Spec.map (CommRingCat.ofHom ρB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  refine IsPullback.of_right ?_ (g2L_bc_snd N₀ q ρA ρB φ hφ)
    (IsPullback.of_hasPullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρA)))
  have h1 := g2L_bc_fst N₀ q ρA ρB φ hφ
  convert IsPullback.of_hasPullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρB)) using 1

private theorem g2L_exists_fst_residue_eq (y : ↥(DRLevel.X N₀ q))
    (hy : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal) :
    ∃ y₀ : ↥(DRLevel.fibre (N₀ := N₀) (IsLocalRing.residue (DRLevel.R q))),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q))))).base y₀ = y := by
  set s := (DRLevel.toBase N₀ q).base y with hs
  have hsm : s = IsLocalRing.closedPoint (DRLevel.R q) := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal (DRLevel.R q) ≤ s.asIdeal := by
      rw [g2L_hϖ, Ideal.span_singleton_le_iff_mem]
      exact hy
    exact ((IsLocalRing.maximalIdeal.isMaximal (DRLevel.R q)).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (DRLevel.R q))) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (DRLevel.R q))
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := DRLevel.toBase N₀ q)
    (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) y
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField (DRLevel.R q))) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

private theorem g2L_isClosedImmersion_fst_residue :
    IsClosedImmersion (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q))))) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.pullback_fst _ _ inferInstance

private theorem g2L_flat_bc_ι :
    Flat (g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (g2L_ι q κ toκ))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (g2L_ι q κ toκ).toAlgebra
    show RingHom.Flat (algebraMap (IsLocalRing.ResidueField (DRLevel.R q)) κ)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat (IsLocalRing.ResidueField (DRLevel.R q)) κ)
  exact MorphismProperty.of_isPullback (g2L_isPullback_bc N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).flip inferInstance

private theorem g2L_surjective_bc_ι :
    Surjective (g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom (g2L_ι q κ toκ))) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint κ,
      (inferInstance : Subsingleton (PrimeSpectrum (IsLocalRing.ResidueField (DRLevel.R q)))).elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (g2L_isPullback_bc N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).flip inferInstance

end Local

section Main
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
  [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]

private theorem g2L_mem_toBase_fst (z : ↥(DRLevel.fibre (N₀ := N₀) toκ)) :
    ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z)).asIdeal := by
  have hsq : (DRLevel.toBase N₀ q).base ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z) =
      (Spec.map (CommRingCat.ofHom toκ)).base ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z) :=
    congr($(pullback.condition (f := DRLevel.toBase N₀ q) (g := Spec.map (CommRingCat.ofHom toκ))).base z)
  rw [hsq]
  change ((q : ℕ) : DRLevel.R q) ∈ (PrimeSpectrum.comap toκ
    ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z)).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]
  exact Ideal.zero_mem _

private theorem g2L_fstmax (cmp : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hmax : ∀ z : ↥(DRLevel.fibre (N₀ := N₀) toκ), z ⤳ cmp.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) → z = cmp.base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)))
    (y : ↥(DRLevel.X N₀ q)) (hy : ((q : ℕ) : DRLevel.R q) ∈ ((DRLevel.toBase N₀ q).base y).asIdeal)
    (h : y ⤳ (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    y = (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  set η := genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)
  set g := g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ) with hg
  set j := pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) with hj
  haveI : IsClosedImmersion j := g2L_isClosedImmersion_fst_residue N₀ q
  haveI : Flat g := g2L_flat_bc_ι N₀ q κ toκ
  have hfac : pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = g ≫ j := (g2L_bc_fst N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).symm
  have hξ : (cmp ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η = j.base (g.base (cmp.base η)) := by
    rw [hfac, g2L_comp_base_apply, g2L_comp_base_apply]
  rw [hξ] at h ⊢
  obtain ⟨y₀, rfl⟩ := g2L_exists_fst_residue_eq N₀ q y hy
  have h₀ : y₀ ⤳ g.base (cmp.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hmax z hz]

private theorem g4L_exists_specializes_fst_eq (x w : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (h : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base w ⤳ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base x) :
    ∃ z : ↥(DRLevel.fibre (N₀ := N₀) toκ), z ⤳ x ∧ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base z = (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base w := by
  set g := g2L_bc N₀ q (IsLocalRing.residue (DRLevel.R q)) toκ (g2L_ι q κ toκ) (g2L_ι_comp_residue q κ toκ) with hg
  set j := pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (DRLevel.R q)))) with hj
  haveI : IsClosedImmersion j := g2L_isClosedImmersion_fst_residue N₀ q
  haveI : Flat g := g2L_flat_bc_ι N₀ q κ toκ
  have hfac : pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = g ≫ j := (g2L_bc_fst N₀ q _ _ _ (g2L_ι_comp_residue q κ toκ)).symm
  rw [hfac, g2L_comp_base_apply, g2L_comp_base_apply] at h
  have h₀ : g.base w ⤳ g.base x := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  exact ⟨z, hz, by rw [hfac, g2L_comp_base_apply, g2L_comp_base_apply, hgz]⟩

end Main

end

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (W₀ : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q), ((b : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W₀.nonunits) → toκ (𝔓.rhoInf b) = 0) ∧
    (∀ 𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      (𝔓.comp κ toκ 1 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιInf (N₀ * q) q).base 𝔯 →
      ¬ (𝔯.asIdeal ≤ RingHom.ker (toκ.comp 𝔓.rhoInf.toRingHom))) := by
  classical
  set η := genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) with hη
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨W, hW0, hW1, hWne, habove, hcomplete⟩ :=
      ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
    have hWeq : W 0 = W₀ := SetLike.ext fun f => (hW0 f).trans (hW₀ f).symm
    subst hWeq
    obtain ⟨-, P, hPmem, -, -, hmin⟩ :=
      ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgInf_span_eq_pair_of_valuationSubring_pair N₀ q hqN W hW0 hW1
        hWne habove hcomplete

    obtain ⟨-, -, hred, -⟩ :=
      ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N₀ q hqN
    have hrad : (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))}).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).mpr hred
    have hinf : Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))} = P 0 ⊓ P 1 := by
      rw [← Ideal.radical_eq_iff.mpr hrad, ← Ideal.sInf_minimalPrimes, hmin, sInf_pair]

    have h6 := ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd N₀ q hqN
    dsimp only at h6
    obtain ⟨-, ⟨htA, -, -, -⟩, h3⟩ := h6
    obtain ⟨-, hs1, hs0⟩ := h3 (W 0) (W 1) hW0 hW1

    have key : ∀ (t u : ↥(modularFunctionFieldFull (N₀ * q))) (ht : t ∈ IgusaScheme.chartAlgInf (N₀ * q) q)
        (hu : u ∈ IgusaScheme.chartAlgInf (N₀ * q) q),
        t ^ q - u ^ (q ^ 2 - 1) ∈ (W 1).nonunits →
        ((t ^ q - u ^ (q ^ 2 - 1) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0 = 1 →
        ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q), ((b : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 0).nonunits) → toκ (𝔓.rhoInf b) = 0 := by
      intro t u ht hu hs1 hs0 b hb
      let sA : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) := ⟨t ^ q - u ^ (q ^ 2 - 1), sub_mem (pow_mem ht _) (pow_mem hu _)⟩
      have hrho : 𝔓.rhoInf sA = 1 := by
        apply Subtype.ext
        rw [𝔓.rhoInf_spec, OneMemClass.coe_one]
        exact hs0
      have hb0 : b ∈ P 0 := (hPmem 0 b).mpr hb
      have hsA1 : sA ∈ P 1 := (hPmem 1 sA).mpr hs1
      have hprod : b * sA ∈ Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N₀ * q) q))} := by
        rw [hinf]
        exact ⟨Ideal.mul_mem_right _ _ hb0, Ideal.mul_mem_left _ _ hsA1⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hprod
      have hc' := congrArg 𝔓.rhoInf hc
      rw [map_mul, map_mul, hrho, mul_one, map_natCast] at hc'
      rw [← hc', map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]
    exact key _ _ htA (IgusaScheme.jInvChartInf (N₀ * q) q).2 hs1 hs0
  ·
    intro 𝔯 h𝔯 hle

    set eκ : ↥(DRLevel.fibre (N₀ := N₀) toκ) := (DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ) with heκ
    have hfst_eκ : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base eκ =
        𝔓.εinf.1.base ((Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ)) := by
      rw [heκ, ← g2L_comp_base_apply, ← g2L_comp_base_apply]
      congr 2
      rw [DRLevel.sectionFibre, pullback.lift_fst]

    set K₀ : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q) :=
      (Spec.map (CommRingCat.ofHom (toκ.comp 𝔓.rhoInf.toRingHom))).base (IsLocalRing.closedPoint κ) with hK₀
    have hK₀as : K₀.asIdeal = RingHom.ker (toκ.comp 𝔓.rhoInf.toRingHom) := by
      rw [hK₀]
      change (PrimeSpectrum.comap (toκ.comp 𝔓.rhoInf.toRingHom) (IsLocalRing.closedPoint κ)).asIdeal = _
      rw [PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot]
      congr 1
      exact (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.maximalIdeal.isMaximal κ).ne_top
    have hfst_eκ' : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base eκ = (IgusaScheme.ιInf (N₀ * q) q).base K₀ := by
      rw [hfst_eκ, 𝔓.εinf_chart, g2L_comp_base_apply, hK₀, ← g2L_comp_base_apply (Spec.map (CommRingCat.ofHom toκ)),
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]

    have hsm : eκ ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ 𝔓.smoothLocus := by
      show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base eκ ∈ (𝔓.smoothLocus : Set ↥(DRLevel.X N₀ q))
      rw [hfst_eκ]
      exact 𝔓.εinf_mem_smoothLocus ⟨_, rfl⟩
    have h0 : eκ ∈ Set.range (𝔓.comp κ toκ 0).base := 𝔓.εinf_mem_comp0 κ toκ ⟨IsLocalRing.closedPoint κ, by rw [heκ]⟩
    have h1not : eκ ∉ Set.range (𝔓.comp κ toκ 1).base := fun h1 =>
      (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter N₀ q hqN 𝔓 κ toκ eκ).mp hsm ⟨h0, h1⟩

    have hsp : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base ((𝔓.comp κ toκ 1).base η) ⤳ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base eκ := by
      rw [hfst_eκ', ← g2L_comp_base_apply, h𝔯]
      have : 𝔯 ⤳ K₀ := (PrimeSpectrum.le_iff_specializes 𝔯 K₀).mp (by rw [← PrimeSpectrum.asIdeal_le_asIdeal, hK₀as]; exact hle)
      exact this.map (IgusaScheme.ιInf (N₀ * q) q).base.hom.continuous

    obtain ⟨z, hz, hzfst⟩ := g4L_exists_specializes_fst_eq N₀ q κ toκ eκ _ hsp
    haveI := 𝔓.comp_isClosedImmersion κ toκ 0
    haveI := 𝔓.comp_isClosedImmersion κ toκ 1
    rcases 𝔓.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    ·
      have hc : (𝔓.comp κ toκ 0).base η ⤳ (𝔓.comp κ toκ 0).base c :=
        (genericPoint_specializes c).map (𝔓.comp κ toκ 0).base.hom.continuous
      have hp : (𝔓.comp κ toκ 0 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η ⤳ (𝔓.comp κ toκ 1 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base η := by
        rw [g2L_comp_base_apply, g2L_comp_base_apply, ← hzfst]
        exact hc.map (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base.hom.continuous
      have heq := g2L_fstmax N₀ q κ toκ (𝔓.comp κ toκ 1) (g2L_eq_of_specializes_c1 N₀ q hqN 𝔓 κ toκ) _
        (by rw [g2L_comp_base_apply]; exact g2L_mem_toBase_fst N₀ q κ toκ _) hp
      exact (ModularCurve.DRModelPackageLevel.mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
        N₀ q hqN 𝔓 κ toκ).2.2 heq
    ·
      exact h1not (hz.mem_closed (𝔓.comp κ toκ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)

end S_ModularCurve_DRModelPackageLevel_apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf (solution)
