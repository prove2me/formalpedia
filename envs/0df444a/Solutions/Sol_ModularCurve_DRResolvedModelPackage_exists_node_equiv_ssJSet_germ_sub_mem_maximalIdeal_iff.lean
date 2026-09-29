-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/92c61e85-395c-51f3-a772-1be735aa9bc9

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
import Theorems.Thm_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff
p2m_attr_erase "instance" "ModularCurve.HpoolLevelRing.instCommRingAfin ModularCurve.HpoolLevelRing.instCommRingLevelRing ModularCurve.HpoolLevelRing.instSMulAway ModularCurve.HpoolLevelRing.instModuleAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraAfinAfinAway ModularCurve.HpoolLevelRing.instModuleAway ModularCurve.HpoolLevelRing.instModuleLevelRing ModularCurve.HpoolLevelRing.instCommRingAfinAway ModularCurve.HpoolLevelRing.instModuleAfinSelf ModularCurve.HpoolLevelRing.instSMulAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraLevelRing ModularCurve.HpoolLevelRing.instAlgebraIntAfinAway ModularCurve.HpoolLevelRing.instIsDomainAfin ModularCurve.HpoolLevelRing.instAlgebraIntAfin ModularCurve.HpoolLevelRing.instSMulLevelRing ModularCurve.HpoolLevelRing.algebraAway ModularCurve.HpoolLevelRing.instAlgebraAfinAwayLevelRing ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve~nodeEquiv AlgebraicCurve IsLocalRing"

namespace ND1E79

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem toκ_eq_iff_germ_sub_mem
    (p : ℕ) [Fact p.Prime] [NeZero p] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hU : (DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))
    (hy : ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))
    (c : k)
    (hc : ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c)) ∈ IsLocalRing.maximalIdeal _)
    (ĵ : O) :
    (toκ ĵ = c ↔
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) hU).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) -
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))
        ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)))) := by

  have hfst : (DRModel.baseChangeMap (p := p) toκ) ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
    simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have hsnd : (DRModel.baseChangeMap (p := p) toκ) ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_snd]

  let g : k → (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) := fun c' =>
    ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c'))

  have hjO : ((DRModel.baseChangeMap (p := p) toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) hU).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) := by
    rw [Scheme.Hom.germ_stalkMap_apply]

    have e1 : ((DRModel.baseChangeMap (p := p) toκ).app ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) = (((DRModel.baseChangeMap (p := p) toκ) ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) := rfl
    rw [e1]

    rw [Scheme.Hom.congr_app hfst ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤), CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply]

    have e2 : TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k =
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map ((TopologicalSpace.Opens.map (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base).map
            (homOfLE (TwoChartIntegralModel.chartFinOpen_le_image_top ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).op).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) := by
      show (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app _).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.map (homOfLE _).op).hom _)) = _
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    rw [e2]
    erw [TopCat.Presheaf.germ_res_apply]
    rfl

  have hcO : ((DRModel.baseChangeMap (p := p) toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
        (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (toκ ĵ))) := by
    rw [Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply]

    congr 1

    have e3 : ((DRModel.baseChangeMap (p := p) toκ).app ⊤).hom (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ)) = (((DRModel.baseChangeMap (p := p) toκ) ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ) := rfl
    rw [e3, hsnd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have e4 : ((Spec.map (CommRingCat.ofHom toκ)).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv (toκ ĵ) := by
      exact (congrArg (fun φ => φ.hom ĵ) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom toκ))).symm
    rw [e4]
    rfl

  have hG : ((DRModel.baseChangeMap (p := p) toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) hU).hom
            (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) -
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)) trivial).hom
            (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))) = g (toκ ĵ) := by
    show _ = (_ : _ →+* _) (_ - _)
    rw [map_sub, map_sub, hjO, hcO]
    rfl

  have hloc : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((DRModel.baseChangeMap (p := p) toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)),
      s ∈ IsLocalRing.maximalIdeal _ ↔ ((DRModel.baseChangeMap (p := p) toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n)).hom s ∈ IsLocalRing.maximalIdeal _ := by
    intro s
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]

  have hval : ∀ c' : k, g c' ∈ IsLocalRing.maximalIdeal _ ↔ c' = c := by
    intro c'
    refine ⟨fun h => ?_, fun h => h ▸ hc⟩
    by_contra hne
    have hunit : IsUnit (g c' - g c) := by
      have hu := TwoChartIntegralModel.isUnit_constSection_sub ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k
        (show IsUnit (c - c') from (sub_ne_zero.mpr (Ne.symm hne)).isUnit)
      have : g c' - g c = ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
          (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
            (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c - TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c')) := by
        simp only [g, map_sub]; ring
      rw [this]
      exact (hu.map _).map _
    have hdiff : g c' - g c ∈ IsLocalRing.maximalIdeal _ := Ideal.sub_mem _ h hc
    exact ((IsLocalRing.mem_maximalIdeal _).mp hdiff) hunit

  rw [hloc, hG]
  exact (hval _).symm

end ND1E79

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ) :
    ∃ a : 𝔛reg.node ≃ ↥(ssJSet p k),
      ∀ n : 𝔛reg.node,
        ∃ hU : ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
          ∀ ĵ : O,
            (toκ ĵ = ((a n : ↥(ssJSet p k)) : k) ↔
              ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)) hU).hom
                  (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) -
                ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)) trivial).hom
                  (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))
                ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)))) := by

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ := ModularCurve.DRModelPackage.exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem p hp 𝔛 k
  refine ⟨𝔛reg.nodeEquiv.trans a, fun n => ?_⟩
  have hU := ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin p hp 𝔛 O k toκ (𝔛reg.nodeEquiv n)
  refine ⟨hU, fun ĵ => ?_⟩
  obtain ⟨hy, hgerm⟩ := ha (𝔛reg.nodeEquiv n)
  rw [Equiv.trans_apply]
  exact ND1E79.toκ_eq_iff_germ_sub_mem p 𝔛 O k toκ (𝔛reg.nodeEquiv n) hU hy _ hgerm ĵ

end S_ModularCurve_DRResolvedModelPackage_exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff (solution)
