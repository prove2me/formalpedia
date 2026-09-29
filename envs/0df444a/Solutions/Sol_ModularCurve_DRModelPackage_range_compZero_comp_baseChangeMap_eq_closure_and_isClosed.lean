-- Prove2me | solution 1 for ModularCurve.DRModelPackage.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/450d0b40-1bd5-57bc-bd75-41a2c72d77b3

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ssJSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage ssJSet DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint DRModel.baseChangeMap_apply_notMem_preimage_basicOpen ssJSet_nonempty ssJSet_finite"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "crossing_card comp_jointly_surjective compInf_isClosedImmersion flat compZero_isClosedImmersion compZero ratModel compInf w baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint"
namespace SpecialFibreMax
p2m_open "ModularCurve.DRModelPackage ModularCurve"

theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

theorem not_surjective_of_crossing (f : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) → ↥(𝔛.ratModel κ).C) :
    ¬ Function.Surjective f := by
  classical
  intro hf
  haveI : Infinite ↥(𝔛.ratModel κ).C := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton (𝔛.ratModel κ).toBase
    exact Set.infinite_univ_iff.mp (Set.infinite_univ_iff.mpr
      (Set.infinite_univ_iff.mp ((h.mono (Set.subset_univ _)))))
  haveI : Infinite ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) := Infinite.of_surjective f hf
  have h0 : Nat.card ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) = 0 := Nat.card_eq_zero_of_infinite
  rw [𝔛.crossing_card κ] at h0
  haveI : Finite ↥(ssJSet p κ) := (ssJSet_finite p κ).to_subtype
  haveI : Nonempty ↥(ssJSet p κ) := (ssJSet_nonempty (q := p) (k := κ)).to_subtype
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ h0

theorem compInf_genericPoint_notMem_range_compZero :
    (𝔛.compInf κ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉ Set.range ⇑(𝔛.compZero κ).base := fun h =>
  haveI := 𝔛.compZero_isClosedImmersion κ
  not_surjective_of_crossing p 𝔛 κ _ (surjective_fst_of_mem_range _ _ h)

theorem compZero_genericPoint_notMem_range_compInf :
    (𝔛.compZero κ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉ Set.range ⇑(𝔛.compInf κ).base := fun h =>
  haveI := 𝔛.compInf_isClosedImmersion κ
  not_surjective_of_crossing p 𝔛 κ _ (surjective_snd_of_mem_range _ _ h)

theorem eq_of_specializes_compInf_genericPoint (z : ↥(pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (hz : z ⤳ (𝔛.compInf κ).base (genericPoint ↥(𝔛.ratModel κ).C)) :
    z = (𝔛.compInf κ).base (genericPoint ↥(𝔛.ratModel κ).C) := by
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  rcases 𝔛.comp_jointly_surjective κ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(𝔛.ratModel κ).C :=
      (𝔛.compInf κ).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.compZero κ).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (compInf_genericPoint_notMem_range_compZero p 𝔛 κ)

theorem eq_of_specializes_compZero_genericPoint (z : ↥(pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (hz : z ⤳ (𝔛.compZero κ).base (genericPoint ↥(𝔛.ratModel κ).C)) :
    z = (𝔛.compZero κ).base (genericPoint ↥(𝔛.ratModel κ).C) := by
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  rcases 𝔛.comp_jointly_surjective κ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.compInf κ).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (compZero_genericPoint_notMem_range_compInf p 𝔛 κ)
  · have hc : c ⤳ genericPoint ↥(𝔛.ratModel κ).C :=
      (𝔛.compZero κ).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] (toκ : O →+* κ)

include hϖ in

theorem toκ_maximalIdeal (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def ι : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal p O hϖ κ toκ)

theorem ι_comp_residue : (ι p O hϖ κ toκ).comp (IsLocalRing.residue O) = toκ :=
  RingHom.ext fun _ => rfl

theorem baseChangeMap_eq_comp :
    DRModel.baseChangeMap (p := p) toκ =
      DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ) ≫ DRModel.baseChangeMap (IsLocalRing.residue O) := by
  apply pullback.hom_ext
  · simp only [DRModel.baseChangeMap, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [DRModel.baseChangeMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ι_comp_residue]

theorem isPullback_baseChangeMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPullback (DRModel.baseChangeMap (p := p) φ)
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show φ.comp (algebraMap ℤ A) = algebraMap ℤ B from RingHom.ext_int _ _]
  have h2 : DRModel.baseChangeMap (p := p) φ ≫ pullback.snd (DRModel.toBase p) _ =
      pullback.snd (DRModel.toBase p) _ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ h2
    (IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
  have h1 : DRModel.baseChangeMap (p := p) φ ≫ pullback.fst (DRModel.toBase p) _ =
      pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  convert IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))) using 1

theorem isClosedImmersion_baseChangeMap_residue :
    IsClosedImmersion (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.of_isPullback (isPullback_baseChangeMap p (IsLocalRing.residue O)).flip inferInstance

include hϖ in

theorem exists_baseChangeMap_residue_eq
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).base y₀ = y := by

  set s := (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y with hs
  have hps : ((p : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm

  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_baseChangeMap p (IsLocalRing.residue O)) y (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

theorem flat_baseChangeMap_ι :
    Flat (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (ι p O hϖ κ toκ))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (ι p O hϖ κ toκ).toAlgebra
    show RingHom.Flat (algebraMap (IsLocalRing.ResidueField O) κ)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat (IsLocalRing.ResidueField O) κ)
  exact MorphismProperty.of_isPullback (isPullback_baseChangeMap p (ι p O hϖ κ toκ)).flip inferInstance

end Local

section Main
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

include hϖ in

theorem eq_of_specializes_aux (i : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hi : ∀ z, z ⤳ i.base (genericPoint ↥(𝔛.ratModel κ).C) → z = i.base (genericPoint ↥(𝔛.ratModel κ).C))
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (i ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) :
    y = (i ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) := by
  set η := genericPoint ↥(𝔛.ratModel κ).C
  set g := DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ) with hg
  set j := DRModel.baseChangeMap (p := p) (IsLocalRing.residue O) with hj
  haveI : IsClosedImmersion j := isClosedImmersion_baseChangeMap_residue p O
  haveI : Flat g := flat_baseChangeMap_ι p O hϖ κ toκ
  have hξ : (i ≫ DRModel.baseChangeMap toκ).base η = j.base (g.base (i.base η)) := by
    rw [baseChangeMap_eq_comp p O hϖ κ toκ]
    rfl
  rw [hξ] at h ⊢

  obtain ⟨y₀, rfl⟩ := exists_baseChangeMap_residue_eq p O hϖ y hy

  have h₀ : y₀ ⤳ g.base (i.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hi z hz]

include hϖ in

theorem eq_of_specializes_compInf
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) :
    y = (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) :=
  eq_of_specializes_aux p 𝔛 O hϖ κ toκ _ (eq_of_specializes_compInf_genericPoint p 𝔛 κ) y hy h

include hϖ in
theorem eq_of_specializes_compZero
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)) :
    y = (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) :=
  eq_of_specializes_aux p 𝔛 O hϖ κ toκ _ (eq_of_specializes_compZero_genericPoint p 𝔛 κ) y hy h

end Main

section Coverage
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

include hϖ in
omit [IsAlgClosed κ] in

theorem exists_baseChangeMap_eq
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ z, (DRModel.baseChangeMap (p := p) toκ).base z = y := by
  obtain ⟨y₀, rfl⟩ := exists_baseChangeMap_residue_eq p O hϖ y hy

  haveI : Surjective (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMap p (ι p O hϖ κ toκ)).flip inferInstance
  obtain ⟨z, rfl⟩ := (Surjective.surj (f := DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ))) y₀
  refine ⟨z, ?_⟩
  rw [baseChangeMap_eq_comp p O hϖ κ toκ]
  rfl

include hϖ in

theorem specializes_or_specializes
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hy : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y ∨
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y := by
  obtain ⟨z, rfl⟩ := exists_baseChangeMap_eq p O hϖ κ toκ y hy
  rcases 𝔛.comp_jointly_surjective κ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · left
    exact ((genericPoint_specializes c).map (𝔛.compInf κ).base.hom.continuous).map
      (DRModel.baseChangeMap toκ).base.hom.continuous
  · right
    exact ((genericPoint_specializes c).map (𝔛.compZero κ).base.hom.continuous).map
      (DRModel.baseChangeMap toκ).base.hom.continuous

end Coverage

section StrictMeet
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

omit [IsLocalRing O] in

theorem specializes_of_mem_closure_range (i : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx : x ∈ closure (Set.range ⇑(i ≫ DRModel.baseChangeMap toκ).base)) :
    (i ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ x := by
  rw [specializes_iff_mem_closure]
  refine closure_minimal ?_ isClosed_closure hx
  rintro _ ⟨c, rfl⟩
  exact specializes_iff_mem_closure.mp
    ((genericPoint_specializes c).map (i ≫ DRModel.baseChangeMap toκ).base.hom.continuous)

include hϖ in

theorem mem_range_compInf_of_specializes
    (hne : (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ≠
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C))
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (hz : (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base ((𝔛.compInf κ).base (genericPoint ↥(𝔛.ratModel κ).C)) ⤳
      (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z) :
    z ∈ Set.range ⇑(𝔛.compInf κ).base := by
  haveI : Flat (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) := flat_baseChangeMap_ι p O hϖ κ toκ
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  obtain ⟨z₁, hz₁, hgz₁⟩ := Flat.generalizingMap (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) hz
  rcases 𝔛.comp_jointly_surjective κ z₁ with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact hz₁.mem_closed (𝔛.compInf κ).isClosedEmbedding.isClosed_range ⟨c, hc⟩
  ·
    exfalso
    apply hne
    symm
    have hV : (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉
        (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
      ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _
    refine eq_of_specializes_compInf p 𝔛 O hϖ κ toκ _ hV ?_

    have h1 : (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (DRModel.baseChangeMap toκ).base z₁ := by
      rw [← hc]
      exact (genericPoint_specializes c).map (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous
    have h2 : (DRModel.baseChangeMap toκ).base z₁ =
        (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) := by
      rw [baseChangeMap_eq_comp p O hϖ κ toκ]
      change (DRModel.baseChangeMap (IsLocalRing.residue O)).base
          ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z₁) =
        (DRModel.baseChangeMap (IsLocalRing.residue O)).base
          ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base ((𝔛.compInf κ).base _))
      rw [hgz₁]
    rw [← h2]
    exact h1

include hϖ in
theorem mem_range_compZero_of_specializes
    (hne : (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ≠
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C))
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (hz : (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base ((𝔛.compZero κ).base (genericPoint ↥(𝔛.ratModel κ).C)) ⤳
      (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z) :
    z ∈ Set.range ⇑(𝔛.compZero κ).base := by
  haveI : Flat (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) := flat_baseChangeMap_ι p O hϖ κ toκ
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  obtain ⟨z₁, hz₁, hgz₁⟩ := Flat.generalizingMap (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)) hz
  rcases 𝔛.comp_jointly_surjective κ z₁ with ⟨c, hc⟩ | ⟨c, hc⟩
  · exfalso
    apply hne
    have hV : (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ∉
        (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
      ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _
    refine eq_of_specializes_compZero p 𝔛 O hϖ κ toκ _ hV ?_
    have h1 : (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (DRModel.baseChangeMap toκ).base z₁ := by
      rw [← hc]
      exact (genericPoint_specializes c).map (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous
    have h2 : (DRModel.baseChangeMap toκ).base z₁ =
        (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) := by
      rw [baseChangeMap_eq_comp p O hϖ κ toκ]
      change (DRModel.baseChangeMap (IsLocalRing.residue O)).base
          ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z₁) =
        (DRModel.baseChangeMap (IsLocalRing.residue O)).base
          ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base ((𝔛.compZero κ).base _))
      rw [hgz₁]
    rw [← h2]
    exact h1
  · exact hz₁.mem_closed (𝔛.compZero κ).isClosedEmbedding.isClosed_range ⟨c, hc⟩

end StrictMeet

end ModularCurve.DRModelPackage.SpecialFibreMax

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage ssJSet DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint DRModel.baseChangeMap_apply_notMem_preimage_basicOpen ssJSet_nonempty ssJSet_finite"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "crossing_card comp_jointly_surjective compInf_isClosedImmersion flat compZero_isClosedImmersion compZero ratModel compInf w baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint"
namespace SpecialFibreMax
p2m_open "ModularCurve.DRModelPackage ModularCurve"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed.ModularCurve Topology"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

omit [IsLocalRing O] in

theorem range_subset_closure_singleton (i : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) :
    Set.range ⇑(i ≫ DRModel.baseChangeMap toκ).base ⊆
      closure {(i ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)} := by
  rintro _ ⟨c, rfl⟩
  exact specializes_iff_mem_closure.mp
    ((genericPoint_specializes c).map (i ≫ DRModel.baseChangeMap toκ).base.hom.continuous)

include hϖ in

theorem specializes_baseChangeMap_ι_of_specializes
    (w z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (h : (DRModel.baseChangeMap (p := p) toκ).base w ⤳ (DRModel.baseChangeMap (p := p) toκ).base z) :
    (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base w ⤳ (DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z := by
  haveI := isClosedImmersion_baseChangeMap_residue p O
  rw [baseChangeMap_eq_comp p O hϖ κ toκ] at h
  change (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).base ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base w) ⤳
    (DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).base ((DRModel.baseChangeMap (p := p) (ι p O hϖ κ toκ)).base z) at h
  exact ((DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)).isClosedEmbedding.isInducing.specializes_iff).mp h

include hϖ in

theorem range_compInf_eq_closure :
    Set.range ⇑(𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base =
      closure {(𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)} := by
  apply le_antisymm (range_subset_closure_singleton p 𝔛 O κ toκ _)
  intro y hy
  have hspec : (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y :=
    specializes_iff_mem_closure.mpr hy

  have hyV : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := fun hyD =>
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _ (hspec.mem_open (TopologicalSpace.Opens.isOpen _) hyD)
  obtain ⟨z, rfl⟩ := exists_baseChangeMap_eq p O hϖ κ toκ y hyV
  have hne := ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
    p 𝔛 O hϖ κ toκ
  have hz := mem_range_compInf_of_specializes p 𝔛 O hϖ κ toκ hne z
    (specializes_baseChangeMap_ι_of_specializes p O hϖ κ toκ _ _ hspec)
  obtain ⟨c, rfl⟩ := hz
  exact ⟨c, rfl⟩

include hϖ in

theorem range_compZero_eq_closure :
    Set.range ⇑(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base =
      closure {(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)} := by
  apply le_antisymm (range_subset_closure_singleton p 𝔛 O κ toκ _)
  intro y hy
  have hspec : (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳ y :=
    specializes_iff_mem_closure.mpr hy
  have hyV : y ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := fun hyD =>
    ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _ (hspec.mem_open (TopologicalSpace.Opens.isOpen _) hyD)
  obtain ⟨z, rfl⟩ := exists_baseChangeMap_eq p O hϖ κ toκ y hyV
  have hne := ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
    p 𝔛 O hϖ κ toκ
  have hz := mem_range_compZero_of_specializes p 𝔛 O hϖ κ toκ hne z
    (specializes_baseChangeMap_ι_of_specializes p O hϖ κ toκ _ _ hspec)
  obtain ⟨c, rfl⟩ := hz
  exact ⟨c, rfl⟩

end ModularCurve.DRModelPackage.SpecialFibreMax

open ModularCurve.DRModelPackage.SpecialFibreMax in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsLocalRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    Set.range ⇑(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base =
        closure {(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C)} ∧
      IsClosed (Set.range ⇑(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base) := by
  have h := range_compZero_eq_closure p 𝔛 O hϖ κ toκ
  exact ⟨h, h ▸ isClosed_closure⟩

end S_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed (solution)
