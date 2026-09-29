-- Prove2me | solution 1 for ModularCurve.MultCovering.FamData.t_zeroChart_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0d583612-7358-5824-a74c-96588d6ad536

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_MultCovering_FamData_goodFamilyZero_mem_zeroChart_integers
import Theorems.Thm_ModularCurve_MultCovering_FamData_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
import Theorems.Thm_ModularCurve_MultCovering_FamData_neg_one_le_ord_nodeSrc_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_eq_zero_of_t_eq_one
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_MultCovering_FamData_hasseExp_le_one_of_orth
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_smith
import Theorems.Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"
set_option autoImplicit false

namespace P2MZX5

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ne_zero_of_ord_ne_zero (v : Place K F) {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem not_isUnit_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : ¬ IsUnit (⟨g, hg⟩ : v.toValuationSubring) := by
  rintro ⟨u, hu⟩
  have h0 := v.ord_coe_unit u
  rw [hu] at h0
  change v.ord g = 0 at h0
  omega

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (not_isUnit_of_ord_pos v hg h))

theorem mem_of_ord_pos (v : Place K F) {g : F} (h : 0 < v.ord g) : g ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (ne_zero_of_ord_ne_zero v h.ne') h.le

theorem ord_algebraMap' (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 :=
  (Place.hasValue_algebraMap v c).ord_eq_zero hc

theorem HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_algebraMap_pos (v : Place K F) {g : F} {a : K}
    (h : 0 < v.ord (g - algebraMap K F a)) : v.HasValue g a := by
  have hm := mem_of_ord_pos v h
  have hI := mem_maximalIdeal_of_ord_pos v hm h
  have hgmem : g ∈ v.toValuationSubring := by
    have := add_mem hm (v.algebraMap_mem' a)
    rwa [sub_add_cancel] at this
  refine ⟨hgmem, ?_⟩
  have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring)
      = ⟨g - algebraMap K F a, hm⟩ + ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := by
    apply Subtype.ext
    show g = (g - algebraMap K F a) + algebraMap K F a
    rw [sub_add_cancel]
  rw [hsplit, map_add, (residue_eq_zero_iff _).mpr hI, zero_add]
  exact (Place.hasValue_algebraMap v a).residue_eq

theorem evalAt_eq_of_hasValue {v : Place K F} (hv : v.IsRational) {g : F} {a : K} (h : v.HasValue g a) :
    v.evalAt g = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv h.mem]
  exact h.residue_eq

end PlaceFacts

section JLine

variable (k : Type*) [Field k] [DecidableEq k]

noncomputable abbrev jB : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

theorem ratFuncEquiv_algebraMap (Q : k[X]) :
    (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap k[X] (RatFunc k) Q) = aeval (jB k) Q := by
  apply Subtype.ext
  change ((IntermediateField.equivOfEq (modularFunctionFieldC_one k).symm
      (RatFunc.algEquivOfTranscendental (jqModC k) _
        (algebraMap (Polynomial k) (RatFunc k) Q)) :
          ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = _
  have hcoe : ∀ (h : IntermediateField.adjoin k {jqModC k} = modularFunctionFieldC k 1)
      (x : ↥(IntermediateField.adjoin k {jqModC k})),
      ((IntermediateField.equivOfEq h x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
        = (x : LaurentSeries k) := fun _ _ => rfl
  rw [hcoe, RatFunc.algEquivOfTranscendental_algebraMap]
  have e1 : (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
        ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q) from rfl,
      ← Polynomial.aeval_algHom_apply]
    rfl
  have e2 : (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (jB k) Q) from rfl, ← Polynomial.aeval_algHom_apply]
    rfl
  exact e1.trans e2.symm

theorem ord_charLGeomPlaceOfPoint_aeval (a : k) (Q : k[X]) (hQ : Q ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (aeval (jB k) Q) = Q.rootMultiplicity a := by
  have hplace : charLGeomPlaceOfPoint k a
      = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
          (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) := rfl
  rw [hplace, ← ratFuncEquiv_algebraMap, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeOfPoint_algebraMap a hQ]

theorem aeval_jB_ne_zero (Q : k[X]) (hQ : Q ≠ 0) : aeval (jB k) Q ≠ 0 := by
  intro h
  apply hQ
  have h' : aeval (jqModC k) Q = 0 := by
    have := congrArg (IntermediateField.val (modularFunctionFieldC k 1)) h
    rw [← Polynomial.aeval_algHom_apply, map_zero] at this
    exact this
  exact (transcendental_iff.mp (transcendental_jqModC k)) Q h'

theorem hasValue_jB (a : k) : (charLGeomPlaceOfPoint k a).HasValue (jB k) a := by
  apply hasValue_of_ord_sub_algebraMap_pos
  have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a
  rw [if_pos rfl] at h
  change (charLGeomPlaceOfPoint k a).ord (jB k - algebraMap k ↥(modularFunctionFieldC k 1) a) = 1 at h
  omega

theorem hasValue_aeval (a : k) (Q : k[X]) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q) (Q.eval a) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, eval_add]
    exact P2MZX5.HasValue.add hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    refine Place.HasValue.mul (Place.hasValue_algebraMap _ c) ?_
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Place.hasValue_one _
    | succ n ih => rw [pow_succ, pow_succ]; exact Place.HasValue.mul ih (hasValue_jB k a)

theorem hasValue_aeval_mul_inv (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q * (aeval (jB k) R)⁻¹) (Q.eval a * (R.eval a)⁻¹) :=
  Place.HasValue.mul (hasValue_aeval k a Q) ((hasValue_aeval k a R).inv hR)

theorem aeval_mul_inv_sub_algebraMap (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    aeval (jB k) Q * (aeval (jB k) R)⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
          * (aeval (jB k) R * algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
  have hR' : aeval (jB k) R ≠ 0 := by
    intro h0
    have := (hasValue_aeval k a R).ne_zero hR
    exact this h0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have e1 : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
      = algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) * aeval (jB k) Q
        - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a) * aeval (jB k) R := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_C]
  have e2 : algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a)
        * (algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
    rw [_root_.map_mul, map_inv₀]
  rw [e1, e2]
  field_simp

theorem ord_aeval_mul_inv_sub_value (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0)
    (hN : C (R.eval a) * Q - C (Q.eval a) * R ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord
        (aeval (jB k) Q * (aeval (jB k) R)⁻¹
          - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹))
      = (C (R.eval a) * Q - C (Q.eval a) * R).rootMultiplicity a := by
  have hR0 : R ≠ 0 := by rintro rfl; exact hR (eval_zero)
  have hR' : aeval (jB k) R ≠ 0 := aeval_jB_ne_zero k R hR0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have hN' : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R) ≠ 0 := aeval_jB_ne_zero k _ hN
  rw [aeval_mul_inv_sub_algebraMap k a Q R hR,
    (charLGeomPlaceOfPoint k a).ord_mul hN' (inv_ne_zero (mul_ne_zero hR' hc)),
    (charLGeomPlaceOfPoint k a).ord_inv, (charLGeomPlaceOfPoint k a).ord_mul hR' hc,
    ord_charLGeomPlaceOfPoint_aeval k a _ hN, ord_charLGeomPlaceOfPoint_aeval k a R hR0, ord_algebraMap' _ hR,
    Polynomial.rootMultiplicity_eq_zero (fun h : IsRoot R a => hR h)]
  simp

end JLine

end P2MZX5

namespace P2MZX5

open Finset Polynomial

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]

theorem sum_mul_sum_sub_sum_mul_sum' (v w c d : ι → K) :
    (∑ i, c i * v i) * (∑ j, d j * w j) - (∑ j, d j * v j) * (∑ i, c i * w i) =
      ∑ i, ∑ j, c i * d j * (v i * w j - v j * w i) := by
  have h1 : ∀ i, ∑ j, c i * d j * (v i * w j - v j * w i)
      = c i * v i * (∑ j, d j * w j) - (∑ j, d j * v j) * (c i * w i) := by
    intro i
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

theorem exists_minor_ne_zero_of_functionals' (v w c d : ι → K)
    (h : (∑ i, c i * v i) * (∑ j, d j * w j) ≠ (∑ j, d j * v j) * (∑ i, c i * w i)) :
    ∃ i j, v i * w j ≠ v j * w i := by
  by_contra hall
  push_neg at hall
  apply h
  rw [← sub_eq_zero, sum_mul_sum_sub_sum_mul_sum']
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [hall i j, sub_self, mul_zero]

section Rows

variable (P : ι → K[X]) (c d : ι → K)
  (hc : ∑ i, c i • P i = 1) (hd : ∑ i, d i • P i = X)

theorem eval_sum_smul (a : ι → K) (b : K) : (∑ i, a i • P i).eval b = ∑ i, a i * (P i).eval b := by
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul]

theorem derivative_eval_sum_smul (a : ι → K) (b : K) :
    (derivative (∑ i, a i • P i)).eval b = ∑ i, a i * (derivative (P i)).eval b := by
  rw [map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_smul, Polynomial.eval_smul, smul_eq_mul]

theorem coeff_sum_smul (a : ι → K) (m : ℕ) : (∑ i, a i • P i).coeff m = ∑ i, a i * (P i).coeff m := by
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_smul, smul_eq_mul]

include hc hd in

theorem exists_eval_minor_ne_zero (b b' : K) (hbb : b ≠ b') :
    ∃ i j, (P i).eval b * (P j).eval b' ≠ (P j).eval b * (P i).eval b' := by
  refine exists_minor_ne_zero_of_functionals' (fun i => (P i).eval b) (fun i => (P i).eval b') c d ?_
  rw [← eval_sum_smul P c b, ← eval_sum_smul P d b', ← eval_sum_smul P d b, ← eval_sum_smul P c b', hc, hd,
    eval_one, eval_one, eval_X, eval_X, one_mul, mul_one]
  exact hbb.symm

include hc hd in

theorem exists_eval_derivative_minor_ne_zero [Nontrivial K] (b : K) :
    ∃ i j, (P i).eval b * (derivative (P j)).eval b ≠ (P j).eval b * (derivative (P i)).eval b := by
  refine exists_minor_ne_zero_of_functionals' (fun i => (P i).eval b) (fun i => (derivative (P i)).eval b)
    c d ?_
  rw [← eval_sum_smul P c b, ← derivative_eval_sum_smul P d b, ← eval_sum_smul P d b,
    ← derivative_eval_sum_smul P c b, hc, hd, eval_one, derivative_X, eval_one, derivative_one, eval_zero,
    one_mul, mul_zero]
  exact one_ne_zero

theorem exists_eval_coeff_minor_ne_zero [Nontrivial K] (m : ℕ) (hm : 1 ≤ m) (e : ι → K)
    (hc : ∑ i, c i • P i = 1) (he : ∑ i, e i • P i = X ^ m) (b : K) :
    ∃ i j, (P i).eval b * (P j).coeff m ≠ (P j).eval b * (P i).coeff m := by
  refine exists_minor_ne_zero_of_functionals' (fun i => (P i).eval b) (fun i => (P i).coeff m) c e ?_
  rw [← eval_sum_smul P c b, ← coeff_sum_smul P e m, ← eval_sum_smul P e b, ← coeff_sum_smul P c m, hc, he,
    eval_one, coeff_X_pow_self, coeff_one, if_neg (by omega), one_mul, mul_zero]
  exact one_ne_zero

end Rows

theorem exists_minor_pivot_ne_zero' {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (v w : ι → K) (c₀ : ι) (hc₀ : v c₀ ≠ 0) (h : ∃ i j, v i * w j ≠ v j * w i) :
    ∃ i, v i * w c₀ ≠ v c₀ * w i := by
  by_contra hall
  push_neg at hall
  obtain ⟨i, j, hij⟩ := h
  apply hij
  have hi := hall i
  have hj := hall j
  have key : v c₀ * (v i * w j - v j * w i) = 0 := by
    have e1 : v c₀ * (v i * w j) = v i * (v c₀ * w j) := by ring
    have e2 : v c₀ * (v j * w i) = v j * (v c₀ * w i) := by ring
    rw [mul_sub, e1, e2, ← hj, ← hi]
    ring
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hc₀
  · exact sub_eq_zero.mp h0

theorem rootMultiplicity_eq_one_of_derivative {K : Type*} [CommRing K] [IsDomain K]
    (N : K[X]) (hN : N ≠ 0) (b : K) (hb : N.eval b = 0) (hd : (derivative N).eval b ≠ 0) :
    N.rootMultiplicity b = 1 := by
  have h1 : 1 ≤ N.rootMultiplicity b := by
    rw [Nat.one_le_iff_ne_zero, Ne, Polynomial.rootMultiplicity_eq_zero_iff, Classical.not_imp]
    exact ⟨Polynomial.IsRoot.def.mpr hb, hN⟩
  have h2 : ¬ 1 < N.rootMultiplicity b := by
    intro hlt
    have := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt
    rw [Function.iterate_one, Polynomial.IsRoot.def] at this
    exact hd this
  omega

end P2MZX5

namespace P2MZX5H

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5"

variable (k : Type*) [Field k] [DecidableEq k]

variable {k}
variable {ι' : Type*} (res : ι' → ↥(modularFunctionFieldC k 1)) (P : ι' → k[X]) (S : k[X]) (hS : S ≠ 0)
  (hres : ∀ i, res i * aeval (jB k) S = aeval (jB k) (P i))

include hS hres in

theorem res_eq (i : ι') : res i = aeval (jB k) (P i) * (aeval (jB k) S)⁻¹ := by
  have hS' := aeval_jB_ne_zero k S hS
  rw [← hres i, mul_inv_cancel_right₀ hS']

include hS hres in

theorem res_mul_inv (i le : ι') :
    res i * (res le)⁻¹ = aeval (jB k) (P i) * (aeval (jB k) (P le))⁻¹ := by
  have hS' := aeval_jB_ne_zero k S hS
  rw [res_eq res P S hS hres i, res_eq res P S hS hres le, mul_inv, inv_inv]
  field_simp

include hS hres in

theorem res_ne_zero (i : ι') (hP : P i ≠ 0) : res i ≠ 0 := by
  rw [res_eq res P S hS hres i]
  exact mul_ne_zero (aeval_jB_ne_zero k _ hP) (inv_ne_zero (aeval_jB_ne_zero k S hS))

include hS hres in
set_option synthInstance.maxHeartbeats 800000 in

theorem linearIndependent_res (hP : LinearIndependent k P) : LinearIndependent k res := by
  rw [linearIndependent_iff'] at hP ⊢
  intro s g hsum i hi

  have h1 : (∑ j ∈ s, g j • res j) * aeval (jB k) S = ∑ j ∈ s, g j • aeval (jB k) (P j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, hres]
  rw [hsum, zero_mul] at h1
  have h2 : aeval (jB k) (∑ j ∈ s, g j • P j) = 0 := by
    rw [_root_.map_sum, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact map_smul (aeval (jB k)) (g j) (P j)
  have h3 : ∑ j ∈ s, g j • P j = 0 := by
    by_contra hne
    exact aeval_jB_ne_zero k _ hne h2
  exact hP s g h3 i hi

end P2MZX5H

namespace P2MZX5H

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5"

variable {k : Type*} [Field k] [DecidableEq k]
variable {ι' : Type*} (res : ι' → ↥(modularFunctionFieldC k 1)) (P : ι' → k[X]) (S : k[X]) (hS : S ≠ 0)
  (hres : ∀ i, res i * aeval (jB k) S = aeval (jB k) (P i))

include hS hres in

theorem hasValue_res_mul_inv (b : k) (i le : ι') (hle : (P le).eval b ≠ 0) :
    (charLGeomPlaceOfPoint k b).HasValue (res i * (res le)⁻¹) ((P i).eval b * ((P le).eval b)⁻¹) := by
  rw [res_mul_inv res P S hS hres i le]
  exact hasValue_aeval_mul_inv k b (P i) (P le) hle

include hS hres in

theorem hasValue_res (b : k) (hb : S.eval b ≠ 0) (i : ι') :
    (charLGeomPlaceOfPoint k b).HasValue (res i) ((P i).eval b * (S.eval b)⁻¹) := by
  rw [res_eq res P S hS hres i]
  exact hasValue_aeval_mul_inv k b (P i) S hb

theorem exists_minor_ne_zero_smul {ι'' : Type*} (v w : ι'' → k) (c d : k) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : ∃ i j, v i * w j ≠ v j * w i) :
    ∃ i j, (v i * c) * (w j * d) ≠ (v j * c) * (w i * d) := by
  obtain ⟨i, j, hij⟩ := h
  refine ⟨i, j, fun heq => hij ?_⟩
  have : (v i * w j - v j * w i) * (c * d) = 0 := by
    have e : (v i * c) * (w j * d) - (v j * c) * (w i * d) = (v i * w j - v j * w i) * (c * d) := by ring
    rw [← e, sub_eq_zero]
    exact heq
  rcases mul_eq_zero.mp this with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (mul_ne_zero hc hd)

theorem exists_rowMinor_ne_zero [Fintype ι'] (cc dd : ι' → k)
    (hc : ∑ i, cc i • P i = 1) (hd : ∑ i, dd i • P i = X)
    (b b' : k) (hbb : b ≠ b') (le le' : ι') (hle : (P le).eval b ≠ 0) (hle' : (P le').eval b' ≠ 0) :
    ∃ i j, ((P i).eval b * ((P le).eval b)⁻¹) * ((P j).eval b' * ((P le').eval b')⁻¹)
      ≠ ((P j).eval b * ((P le).eval b)⁻¹) * ((P i).eval b' * ((P le').eval b')⁻¹) :=
  exists_minor_ne_zero_smul (fun i => (P i).eval b) (fun i => (P i).eval b') _ _ (inv_ne_zero hle) (inv_ne_zero hle')
    (exists_eval_minor_ne_zero P cc dd hc hd b b' hbb)

theorem exists_rowMinor_infty_ne_zero [Fintype ι'] (m : ℕ) (hm : 1 ≤ m) (cc ee : ι' → k)
    (hc : ∑ i, cc i • P i = 1) (he : ∑ i, ee i • P i = X ^ m)
    (b : k) (le cinf : ι') (hle : (P le).eval b ≠ 0) (hcinf : (P cinf).coeff m ≠ 0) :
    ∃ i j, ((P i).eval b * ((P le).eval b)⁻¹) * ((P j).coeff m * ((P cinf).coeff m)⁻¹)
      ≠ ((P j).eval b * ((P le).eval b)⁻¹) * ((P i).coeff m * ((P cinf).coeff m)⁻¹) :=
  exists_minor_ne_zero_smul (fun i => (P i).eval b) (fun i => (P i).coeff m) _ _ (inv_ne_zero hle) (inv_ne_zero hcinf)
    (exists_eval_coeff_minor_ne_zero P cc m hm ee hc he b)

include hS hres in

theorem exists_ord_res_mul_inv_sub_eq_one [Fintype ι'] (cc dd : ι' → k)
    (hc : ∑ i, cc i • P i = 1) (hd : ∑ i, dd i • P i = X)
    (b : k) (c₀ : ι') (hc₀ : (P c₀).eval b ≠ 0) :
    ∃ i, (charLGeomPlaceOfPoint k b).ord
        (res i * (res c₀)⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) ((P i).eval b * ((P c₀).eval b)⁻¹)) = 1 := by

  obtain ⟨i, hi⟩ := exists_minor_pivot_ne_zero' (fun i => (P i).eval b) (fun i => (derivative (P i)).eval b) c₀ hc₀
    (exists_eval_derivative_minor_ne_zero P cc dd hc hd b)
  refine ⟨i, ?_⟩

  set N : k[X] := C ((P c₀).eval b) * P i - C ((P i).eval b) * P c₀ with hN
  have hNb : N.eval b = 0 := by
    rw [hN, eval_sub, eval_mul, eval_mul, eval_C, eval_C]
    ring
  have hNd : (derivative N).eval b ≠ 0 := by
    rw [hN, derivative_sub, derivative_mul, derivative_mul, derivative_C, derivative_C, zero_mul, zero_mul, zero_add,
      zero_add, eval_sub, eval_mul, eval_mul, eval_C, eval_C]
    intro h0
    apply hi

    have : (P c₀).eval b * (derivative (P i)).eval b - (P i).eval b * (derivative (P c₀)).eval b = 0 := h0
    have := sub_eq_zero.mp this
    rw [this.symm]
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, derivative_zero, eval_zero] at hNd
    exact hNd rfl
  rw [res_mul_inv res P S hS hres i c₀, ord_aeval_mul_inv_sub_value k b (P i) (P c₀) hc₀ hN0,
    rootMultiplicity_eq_one_of_derivative N hN0 b hNb hNd]
  rfl

end P2MZX5H

namespace P2MZX5

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing"

section Infty

variable (k : Type*) [Field k] [DecidableEq k] [DecidableEq (RatFunc k)]

noncomputable abbrev vInf : Place k ↥(modularFunctionFieldC k 1) :=
  charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)

theorem ord_vInf_aeval (Q : k[X]) (hQ : Q ≠ 0) :
    (vInf k).ord (aeval (jB k) Q) = -(Q.natDegree : ℤ) := by
  have hplace : vInf k
      = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
          (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeInfty k) := rfl
  rw [hplace, ← ratFuncEquiv_algebraMap, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeInfty_algebraMap hQ]

theorem ord_vInf_aeval_mul_inv (Q S : k[X]) (hQ : Q ≠ 0) (hS : S ≠ 0) :
    (vInf k).ord (aeval (jB k) Q * (aeval (jB k) S)⁻¹) = (S.natDegree : ℤ) - (Q.natDegree : ℤ) := by
  rw [(vInf k).ord_mul (aeval_jB_ne_zero k Q hQ) (inv_ne_zero (aeval_jB_ne_zero k S hS)), (vInf k).ord_inv,
    ord_vInf_aeval k Q hQ, ord_vInf_aeval k S hS]
  ring

theorem hasValue_vInf_aeval_mul_inv (m : ℕ) (Q S : k[X]) (hS : S.natDegree = m) (hS0 : S ≠ 0)
    (hQ : Q.natDegree ≤ m) :
    (vInf k).HasValue (aeval (jB k) Q * (aeval (jB k) S)⁻¹) (Q.coeff m * (S.leadingCoeff)⁻¹) := by
  set c : k := Q.coeff m * (S.leadingCoeff)⁻¹ with hc
  have hS' := aeval_jB_ne_zero k S hS0
  have hlc : S.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hS0

  have hdiff : aeval (jB k) Q * (aeval (jB k) S)⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) c
      = aeval (jB k) (Q - C c * S) * (aeval (jB k) S)⁻¹ := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C]
    field_simp
  by_cases hN : Q - C c * S = 0
  ·
    have : aeval (jB k) Q * (aeval (jB k) S)⁻¹ = algebraMap k ↥(modularFunctionFieldC k 1) c := by
      rw [← sub_eq_zero, hdiff, hN, map_zero, zero_mul]
    rw [this]
    exact Place.hasValue_algebraMap _ c
  · apply hasValue_of_ord_sub_algebraMap_pos
    rw [hdiff, ord_vInf_aeval_mul_inv k _ S hN hS0, hS]

    have hdeg : (Q - C c * S).natDegree < m := by
      have hle : (Q - C c * S).natDegree ≤ m := by
        refine (natDegree_sub_le _ _).trans (max_le hQ ?_)
        exact (natDegree_C_mul_le _ _).trans hS.le
      rcases Nat.lt_or_ge (Q - C c * S).natDegree m with h | h
      · exact h
      · exfalso
        have heq : (Q - C c * S).natDegree = m := le_antisymm hle h
        have hcoeff : (Q - C c * S).coeff m = 0 := by
          rw [coeff_sub, coeff_C_mul, hc]
          have : S.coeff m = S.leadingCoeff := by rw [Polynomial.leadingCoeff, hS]
          rw [this]
          field_simp
          ring
        have := leadingCoeff_ne_zero.mpr hN
        rw [Polynomial.leadingCoeff, heq, hcoeff] at this
        exact this rfl
    omega

end Infty

end P2MZX5

namespace P2MZX5

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing Finset"

section ImmInfty

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]

theorem exists_coeff_coeff_minor_ne_zero [Nontrivial K] (P : ι → K[X]) (m : ℕ) (hm : 1 ≤ m) (e f : ι → K)
    (he : ∑ i, e i • P i = X ^ m) (hf : ∑ i, f i • P i = X ^ (m - 1)) :
    ∃ i j, (P i).coeff m * (P j).coeff (m - 1) ≠ (P j).coeff m * (P i).coeff (m - 1) := by
  refine exists_minor_ne_zero_of_functionals' (fun i => (P i).coeff m) (fun i => (P i).coeff (m - 1)) e f ?_
  rw [← coeff_sum_smul P e m, ← coeff_sum_smul P f (m - 1), ← coeff_sum_smul P f m, ← coeff_sum_smul P e (m - 1),
    he, hf, coeff_X_pow_self, coeff_X_pow_self, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega),
    one_mul, mul_zero]
  exact one_ne_zero

end ImmInfty

section ImmInfty2

variable (k : Type*) [Field k] [DecidableEq k] [DecidableEq (RatFunc k)]
variable {ι' : Type*} [Fintype ι']

theorem exists_ord_vInf_sub_eq_one (P : ι' → k[X]) (m : ℕ) (hm : 1 ≤ m) (hdeg : ∀ i, (P i).natDegree ≤ m)
    (e f : ι' → k) (he : ∑ i, e i • P i = X ^ m) (hf : ∑ i, f i • P i = X ^ (m - 1))
    (c₀ : ι') (hc₀ : (P c₀).natDegree = m) (hc₀0 : P c₀ ≠ 0) :
    ∃ i, (vInf k).ord (aeval (jB k) (P i) * (aeval (jB k) (P c₀))⁻¹
        - algebraMap k ↥(modularFunctionFieldC k 1) ((P i).coeff m * ((P c₀).leadingCoeff)⁻¹)) = 1 := by
  have hlc : (P c₀).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hc₀0
  have hlc' : (P c₀).coeff m = (P c₀).leadingCoeff := by rw [Polynomial.leadingCoeff, hc₀]

  obtain ⟨i, hi⟩ := exists_minor_pivot_ne_zero' (fun i => (P i).coeff m) (fun i => (P i).coeff (m - 1)) c₀
    (show (P c₀).coeff m ≠ 0 by rw [hlc']; exact hlc) (exists_coeff_coeff_minor_ne_zero P m hm e f he hf)
  refine ⟨i, ?_⟩
  set c : k := (P i).coeff m * ((P c₀).leadingCoeff)⁻¹ with hc
  set N : k[X] := P i - C c * P c₀ with hN
  have hdiff : aeval (jB k) (P i) * (aeval (jB k) (P c₀))⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) c
      = aeval (jB k) N * (aeval (jB k) (P c₀))⁻¹ := by
    have hS' := aeval_jB_ne_zero k (P c₀) hc₀0
    rw [hN, Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C]
    field_simp

  have hNm : N.coeff m = 0 := by
    rw [hN, coeff_sub, coeff_C_mul, hc, hlc']
    field_simp
    ring
  have hNm1 : N.coeff (m - 1) ≠ 0 := by
    rw [hN, coeff_sub, coeff_C_mul, hc]
    intro h0
    apply hi

    rw [hlc']
    have h1 : (P i).coeff (m - 1) = (P i).coeff m * ((P c₀).leadingCoeff)⁻¹ * (P c₀).coeff (m - 1) :=
      sub_eq_zero.mp h0
    rw [h1]
    field_simp
  have hN0 : N ≠ 0 := fun h => hNm1 (by rw [h, coeff_zero])
  have hNdeg : N.natDegree = m - 1 := by
    have hle : N.natDegree ≤ m := by
      rw [hN]
      refine (natDegree_sub_le _ _).trans (max_le (hdeg i) ?_)
      exact (natDegree_C_mul_le _ _).trans (hdeg c₀)
    have hlt : N.natDegree < m := by
      rcases Nat.lt_or_ge N.natDegree m with h | h
      · exact h
      · exfalso
        have heq : N.natDegree = m := le_antisymm hle h
        have := leadingCoeff_ne_zero.mpr hN0
        rw [Polynomial.leadingCoeff, heq, hNm] at this
        exact this rfl
    have hge : m - 1 ≤ N.natDegree := le_natDegree_of_ne_zero hNm1
    omega
  rw [hdiff, ord_vInf_aeval_mul_inv k N (P c₀) hN0 hc₀0, hc₀, hNdeg]
  omega

end ImmInfty2

end P2MZX5

namespace P2MZX5G

open AlgebraicCurve IsLocalRing

variable {L F Fbar : Type*} [Field L] [Field F] [Algebra L F] [Field Fbar]
  {A : ValuationSubring L} [Algebra (ResidueField A) Fbar]

theorem isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers)
    (hres : C.residue ⟨g, hg⟩ ≠ 0) : IsUnit (⟨g, hg⟩ : C.integers) := by
  by_contra hu
  apply hres
  have hmem : (⟨g, hg⟩ : C.integers) ∈ maximalIdeal C.integers := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  rw [← C.ker_residue] at hmem
  exact (RingHom.mem_ker).mp hmem

theorem residue_mul_inv (C : ComponentChart A F Fbar) {f g : F} (hf : f ∈ C.integers) (hg : g ∈ C.integers)
    (hres : C.residue ⟨g, hg⟩ ≠ 0) :
    ∃ h : f * g⁻¹ ∈ C.integers, C.residue ⟨f * g⁻¹, h⟩ = C.residue ⟨f, hf⟩ * (C.residue ⟨g, hg⟩)⁻¹ := by
  obtain ⟨u, hu⟩ := isUnit_of_residue_ne_zero C hg hres
  have hcoe : ((u : C.integers) : F) = g := by rw [hu]
  have hinv : (((u⁻¹ : C.integersˣ) : C.integers) : F) = g⁻¹ := by
    have h1 : g * (((u⁻¹ : C.integersˣ) : C.integers) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hgi : g⁻¹ ∈ C.integers := hinv ▸ SetLike.coe_mem _
  refine ⟨mul_mem hf hgi, ?_⟩
  have hx : (⟨f * g⁻¹, mul_mem hf hgi⟩ : C.integers) = ⟨f, hf⟩ * ((u⁻¹ : C.integersˣ) : C.integers) :=
    Subtype.ext (by rw [MulMemClass.coe_mul, hinv])
  rw [hx, map_mul, map_units_inv, hu]

theorem hasValue_residue_of_pointwise (C : ComponentChart A F Fbar) {P : Place L F} (hP : P ∈ C.dom)
    (hrat : P.IsRational) {f : F} (hf : f ∈ C.integers)
    (hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f ∈ w.toValuationSubring) :
    ∃ h : P.evalAt f ∈ A,
      (C.placeMap P).HasValue (C.residue ⟨f, hf⟩) (IsLocalRing.residue A ⟨P.evalAt f, h⟩) := by
  obtain ⟨hm, h, heq⟩ := C.pointwise P hP hrat f hf hfib
  exact ⟨h, hm, heq.symm⟩

end P2MZX5G

namespace P2MZX5C

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5 P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5H P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5G"

set_option synthInstance.maxHeartbeats 1600000 in

noncomputable scoped instance instAlgebraFbar37 (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Algebra (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) := inferInstance

set_option synthInstance.maxHeartbeats 1600000

variable {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (ResidueField ↥A)] [DecidableEq (RatFunc (ResidueField ↥A))]
  {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem placeMap_cases (C : ComponentChart A F ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (SS : Set (ResidueField ↥A))
    (hnodes : ∀ x, x ∈ C.nodes ↔ ∃ a ∈ SS, charLGeomPlaceOfPoint (ResidueField ↥A) a = x)
    (hclass : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      (∃ c, v = charLGeomPlaceOfPoint (ResidueField ↥A) c) ∨ v = vInf (ResidueField ↥A))
    (W : Place (AlgebraicClosure ℚ) F) (hW : W ∈ C.dom) :
    (∃ b, C.placeMap W = charLGeomPlaceOfPoint (ResidueField ↥A) b ∧ b ∉ SS) ∨ C.placeMap W = vInf (ResidueField ↥A) := by
  rcases hclass (C.placeMap W) with ⟨c, hc⟩ | h
  · refine Or.inl ⟨c, hc, fun hss => C.placeMap_not_mem_nodes W hW ?_⟩
    exact (hnodes _).mpr ⟨c, hss, hc.symm⟩
  · exact Or.inr h

variable (C : ComponentChart A F ↥(modularFunctionFieldC (ResidueField ↥A) 1)) {r : ℕ} (t' : Fin r → F) (hint : ∀ i, t' i ∈ C.integers)
  (P : Fin r → (ResidueField ↥A)[X]) (S : (ResidueField ↥A)[X]) (hS : S ≠ 0)
  (hres : ∀ i, C.residue ⟨t' i, hint i⟩ * aeval (jB (ResidueField ↥A)) S = aeval (jB (ResidueField ↥A)) (P i))

include hS hres in

theorem exists_residue_ratio (i le : Fin r) (hle : P le ≠ 0) :
    ∃ h : t' i * (t' le)⁻¹ ∈ C.integers,
      C.residue ⟨t' i * (t' le)⁻¹, h⟩ = C.residue ⟨t' i, hint i⟩ * (C.residue ⟨t' le, hint le⟩)⁻¹ :=
  residue_mul_inv C (hint i) (hint le)
    (res_ne_zero (fun i => C.residue ⟨t' i, hint i⟩) P S hS hres le hle)

include hS hres in

theorem hasValue_residue_ratio (b : ResidueField ↥A) (i le : Fin r) (hle : (P le).eval b ≠ 0) :
    ∃ h : t' i * (t' le)⁻¹ ∈ C.integers,
      (charLGeomPlaceOfPoint (ResidueField ↥A) b).HasValue (C.residue ⟨t' i * (t' le)⁻¹, h⟩)
        ((P i).eval b * ((P le).eval b)⁻¹) := by
  have hle0 : P le ≠ 0 := by rintro h0; rw [h0, eval_zero] at hle; exact hle rfl
  obtain ⟨h, hh⟩ := exists_residue_ratio C t' hint P S hS hres i le hle0
  refine ⟨h, ?_⟩
  rw [hh]
  exact hasValue_res_mul_inv (fun i => C.residue ⟨t' i, hint i⟩) P S hS hres b i le hle

include hS hres in

theorem evalAt_residue_ratio (b : ResidueField ↥A) (i le : Fin r) (hle : (P le).eval b ≠ 0) :
    ∃ h : t' i * (t' le)⁻¹ ∈ C.integers,
      (charLGeomPlaceOfPoint (ResidueField ↥A) b).evalAt (C.residue ⟨t' i * (t' le)⁻¹, h⟩)
        = (P i).eval b * ((P le).eval b)⁻¹ := by
  obtain ⟨h, hv⟩ := hasValue_residue_ratio C t' hint P S hS hres b i le hle
  refine ⟨h, evalAt_eq_of_hasValue ?_ hv⟩
  exact (Place.isRational_iff_deg_eq_one _).mpr (deg_charLGeomPlaceOfPoint (ResidueField ↥A) b)

end P2MZX5C
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

namespace P2MZX5MC

p2m_open "AlgebraicCurve ModularCurve~jBar ModularCurve.MultCovering Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5 P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5H P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5G P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (ResidueField ↥A)] [DecidableEq (RatFunc (ResidueField ↥A))] [CharP (ResidueField ↥A) p]
  (Γ : ChartCtx p A)

noncomputable def ssSharp : (ResidueField ↥A)[X] := ∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e ^ p))

theorem ssSharp_ne_zero : ssSharp Γ ≠ 0 := by
  unfold ssSharp
  exact Finset.prod_ne_zero_iff.mpr fun e _ => X_sub_C_ne_zero _

theorem natDegree_ssSharp : (ssSharp Γ).natDegree = mAnnuli p := by
  unfold ssSharp
  rw [natDegree_prod_of_monic _ _ (fun e _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem eval_ssSharp_ne_zero_iff (b : ResidueField ↥A) :
    (ssSharp Γ).eval b ≠ 0 ↔ ∀ e, b ≠ ssValue Γ e ^ p := by
  unfold ssSharp
  rw [eval_prod, Finset.prod_ne_zero_iff]
  simp [sub_ne_zero]

theorem mem_zeroChart_nodes_iff' (x : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
    x ∈ (zeroChart Γ).nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x := by
  show x ∈ (infChart Γ).nodes ↔ _
  exact (Γ.hWn x).trans (Γ.supply.mem_ssPlaces_iff x)

theorem zeroChart_placeMap_cases
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : W ∈ (zeroChart Γ).dom) :
    (∃ b, (zeroChart Γ).placeMap W = charLGeomPlaceOfPoint (ResidueField ↥A) b ∧ b ∉ ssJSet p (ResidueField ↥A)) ∨
      (zeroChart Γ).placeMap W = vInf (ResidueField ↥A) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact placeMap_cases (zeroChart Γ) (ssJSet p (ResidueField ↥A)) (mem_zeroChart_nodes_iff' Γ)
    (fun v => ModularCurve.eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (ResidueField ↥A) v) W hW

theorem eval_ssSharp_ne_zero_of_not_mem {b : ResidueField ↥A} (hb : b ∉ ssJSet p (ResidueField ↥A)) :
    (ssSharp Γ).eval b ≠ 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  rw [eval_ssSharp_ne_zero_iff]
  rintro e rfl
  exact hb ((ModularCurve.pow_mem_ssJSet_iff_of_perfectField p (ssValue Γ e)).mpr (ssValue_mem_ssJSet Γ e))

theorem ssValue_pow_injective : Function.Injective fun e : Fin (mAnnuli p) => ssValue Γ e ^ p := by
  intro e e' h
  apply ssValue_injective Γ
  exact frobenius_inj (ResidueField ↥A) p h

section Xi

variable {r : ℕ} (t' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hint : ∀ i, t' i ∈ (zeroChart Γ).integers)
  (P : Fin r → (ResidueField ↥A)[X])
  (hres : ∀ i, (zeroChart Γ).residue ⟨t' i, hint i⟩ * aeval (jB (ResidueField ↥A)) (ssSharp Γ)
    = aeval (jB (ResidueField ↥A)) (P i))

noncomputable def nodeRow (e : Fin (mAnnuli p)) (le : Fin r) : Fin r → ResidueField ↥A :=
  fun i => (P i).eval (ssValue Γ e ^ p) * ((P le).eval (ssValue Γ e ^ p))⁻¹

include hres in

theorem nodeRow_spec (e : Fin (mAnnuli p)) (le : Fin r) (hle : (P le).eval (ssValue Γ e ^ p) ≠ 0) (i : Fin r) :
    ∃ h : t' i * (t' le)⁻¹ ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨t' i * (t' le)⁻¹, h⟩ ∈ (nodeSrc Γ e).toValuationSubring ∧
      (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨t' i * (t' le)⁻¹, h⟩) = nodeRow Γ P e le i := by
  obtain ⟨h, hv⟩ := hasValue_residue_ratio (zeroChart Γ) t' hint P (ssSharp Γ) (ssSharp_ne_zero Γ) hres
    (ssValue Γ e ^ p) i le hle
  refine ⟨h, hv.mem, ?_⟩
  exact evalAt_eq_of_hasValue
    ((Place.isRational_iff_deg_eq_one _).mpr (deg_charLGeomPlaceOfPoint (ResidueField ↥A) _)) hv

theorem nodeRow_sep_node (cc dd : Fin r → ResidueField ↥A)
    (hc : ∑ i, cc i • P i = 1) (hd : ∑ i, dd i • P i = X)
    (e e' : Fin (mAnnuli p)) (hee : e ≠ e') (le le' : Fin r)
    (hle : (P le).eval (ssValue Γ e ^ p) ≠ 0) (hle' : (P le').eval (ssValue Γ e' ^ p) ≠ 0) :
    ∃ i j, nodeRow Γ P e le i * nodeRow Γ P e' le' j ≠ nodeRow Γ P e le j * nodeRow Γ P e' le' i :=
  exists_rowMinor_ne_zero P cc dd hc hd _ _ (fun h => hee (ssValue_pow_injective Γ h)) le le' hle hle'

theorem nodeRow_sep_point (cc dd : Fin r → ResidueField ↥A)
    (hc : ∑ i, cc i • P i = 1) (hd : ∑ i, dd i • P i = X)
    (e : Fin (mAnnuli p)) (le : Fin r) (hle : (P le).eval (ssValue Γ e ^ p) ≠ 0)
    (b : ResidueField ↥A) (hb : b ∉ ssJSet p (ResidueField ↥A)) (c₀ : Fin r) (hc₀ : (P c₀).eval b ≠ 0) :
    ∃ i j, nodeRow Γ P e le i * ((P j).eval b * ((P c₀).eval b)⁻¹)
      ≠ nodeRow Γ P e le j * ((P i).eval b * ((P c₀).eval b)⁻¹) := by
  have hne : ssValue Γ e ^ p ≠ b := by
    intro h
    have := (eval_ssSharp_ne_zero_iff Γ b).mp (eval_ssSharp_ne_zero_of_not_mem Γ hb) e
    exact this h.symm
  exact exists_rowMinor_ne_zero P cc dd hc hd _ _ hne le c₀ hle hc₀

theorem nodeRow_sep_infty (hm : 1 ≤ mAnnuli p) (cc ee : Fin r → ResidueField ↥A)
    (hc : ∑ i, cc i • P i = 1) (he : ∑ i, ee i • P i = X ^ mAnnuli p)
    (e : Fin (mAnnuli p)) (le : Fin r) (hle : (P le).eval (ssValue Γ e ^ p) ≠ 0)
    (cinf : Fin r) (hcinf : (P cinf).coeff (mAnnuli p) ≠ 0) :
    ∃ i j, nodeRow Γ P e le i * ((P j).coeff (mAnnuli p) * ((P cinf).coeff (mAnnuli p))⁻¹)
      ≠ nodeRow Γ P e le j * ((P i).coeff (mAnnuli p) * ((P cinf).coeff (mAnnuli p))⁻¹) :=
  exists_rowMinor_infty_ne_zero P (mAnnuli p) hm cc ee hc he _ le cinf hle hcinf

end Xi
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

end P2MZX5MC
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

namespace P2MZX5MC

p2m_open "AlgebraicCurve ModularCurve~jBar ModularCurve.MultCovering Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5 P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5H P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5G P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

section Bridge
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ssPolyBarZero_eq_aeval : ssPolyBarZero Γ = aeval (jB (ResidueField ↥A)) (ssSharp Γ) := by
  unfold ssPolyBarZero ssSharp
  rw [_root_.map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem one_le_mAnnuli (hp5 : 5 ≤ p) : 1 ≤ mAnnuli p := by
  have hp : p.Prime := Fact.out
  unfold mAnnuli
  by_cases h12 : 12 ≤ p
  · have : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    omega
  · have hlt : p < 12 := Nat.lt_of_not_le h12
    interval_cases p <;> first | decide | exact absurd hp (by norm_num)

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

section D3
variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [DecidableEq (RatFunc (ResidueField ↥A))] [CharP (ResidueField ↥A) p]
  (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r) (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728)

include hA hw in

theorem zxHint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers :=
  (zeroChart_residue_goodFamilyZero_smith p A hA Γ Φ hw).choose

noncomputable def zxP : Fin r → (ResidueField ↥A)[X] :=
  (zeroChart_residue_goodFamilyZero_smith p A hA Γ Φ hw).choose_spec.choose

theorem zxP_spec :
    (∀ l, (zxP p A hA Γ Φ hw l).natDegree ≤ mAnnuli p) ∧
    LinearIndependent (ResidueField ↥A) (zxP p A hA Γ Φ hw) ∧
    (∀ Q : (ResidueField ↥A)[X], Q.natDegree ≤ mAnnuli p →
      Q ∈ Submodule.span (ResidueField ↥A) (Set.range (zxP p A hA Γ Φ hw))) ∧
    (∀ l : Fin r, (l : ℕ) = 0 →
      zxP p A hA Γ Φ hw l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
    ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, zxHint p A hA Γ Φ hw l⟩ * ssPolyBarZero Γ
      = Polynomial.aeval (jBar (ResidueField ↥A)) (zxP p A hA Γ Φ hw l) :=
  (zeroChart_residue_goodFamilyZero_smith p A hA Γ Φ hw).choose_spec.choose_spec

theorem zx_hres : ∀ i, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, zxHint p A hA Γ Φ hw i⟩
      * aeval (jB (ResidueField ↥A)) (ssSharp Γ) = aeval (jB (ResidueField ↥A)) (zxP p A hA Γ Φ hw i) := by
  intro i
  rw [← ssPolyBarZero_eq_aeval]
  exact (zxP_spec p A hA Γ Φ hw).2.2.2.2 i

theorem exists_coeffs (Q : (ResidueField ↥A)[X]) (hQ : Q.natDegree ≤ mAnnuli p) :
    ∃ c : Fin r → ResidueField ↥A, ∑ i, c i • zxP p A hA Γ Φ hw i = Q :=
  (Submodule.mem_span_range_iff_exists_fun (ResidueField ↥A)).mp ((zxP_spec p A hA Γ Φ hw).2.2.1 Q hQ)

noncomputable def zeroChart_nodeRow (e : Fin (mAnnuli p)) (le : Fin r) : Fin r → ResidueField ↥A :=
  nodeRow Γ (zxP p A hA Γ Φ hw) e le

theorem zeroChart_nodeRow_spec (e : Fin (mAnnuli p)) (le : Fin r)
    (hle : (zxP p A hA Γ Φ hw le).eval (ssValue Γ e ^ p) ≠ 0) (i : Fin r) :
    ∃ h : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨_, h⟩ ∈ (nodeSrc Γ e).toValuationSubring ∧
      (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨_, h⟩) = zeroChart_nodeRow p A hA Γ Φ hw e le i :=
  nodeRow_spec Γ (goodFamilyZero Φ.toFamData) (zxHint p A hA Γ Φ hw) (zxP p A hA Γ Φ hw)
    (zx_hres p A hA Γ Φ hw) e le hle i

include hp5 in

theorem zeroChart_nodeRow_sep_node (e e' : Fin (mAnnuli p)) (hee : e ≠ e') (le le' : Fin r)
    (hle : (zxP p A hA Γ Φ hw le).eval (ssValue Γ e ^ p) ≠ 0)
    (hle' : (zxP p A hA Γ Φ hw le').eval (ssValue Γ e' ^ p) ≠ 0) :
    ∃ i j, zeroChart_nodeRow p A hA Γ Φ hw e le i * zeroChart_nodeRow p A hA Γ Φ hw e' le' j
      ≠ zeroChart_nodeRow p A hA Γ Φ hw e le j * zeroChart_nodeRow p A hA Γ Φ hw e' le' i := by
  obtain ⟨cc, hc⟩ := exists_coeffs p A hA Γ Φ hw 1 (by rw [natDegree_one]; exact Nat.zero_le _)
  obtain ⟨dd, hd⟩ := exists_coeffs p A hA Γ Φ hw X (by rw [natDegree_X]; exact one_le_mAnnuli hp5)
  exact nodeRow_sep_node Γ (zxP p A hA Γ Φ hw) cc dd hc hd e e' hee le le' hle hle'

include hp5 in

theorem zeroChart_nodeRow_sep_point (e : Fin (mAnnuli p)) (le : Fin r)
    (hle : (zxP p A hA Γ Φ hw le).eval (ssValue Γ e ^ p) ≠ 0)
    (b : ResidueField ↥A) (hb : b ∉ ssJSet p (ResidueField ↥A)) (c₀ : Fin r)
    (hc₀ : (zxP p A hA Γ Φ hw c₀).eval b ≠ 0) :
    ∃ i j, zeroChart_nodeRow p A hA Γ Φ hw e le i
        * ((zxP p A hA Γ Φ hw j).eval b * ((zxP p A hA Γ Φ hw c₀).eval b)⁻¹)
      ≠ zeroChart_nodeRow p A hA Γ Φ hw e le j
        * ((zxP p A hA Γ Φ hw i).eval b * ((zxP p A hA Γ Φ hw c₀).eval b)⁻¹) := by
  obtain ⟨cc, hc⟩ := exists_coeffs p A hA Γ Φ hw 1 (by rw [natDegree_one]; exact Nat.zero_le _)
  obtain ⟨dd, hd⟩ := exists_coeffs p A hA Γ Φ hw X (by rw [natDegree_X]; exact one_le_mAnnuli hp5)
  exact nodeRow_sep_point Γ (zxP p A hA Γ Φ hw) cc dd hc hd e le hle b hb c₀ hc₀

include hp5 in

theorem zeroChart_nodeRow_sep_infty (e : Fin (mAnnuli p)) (le : Fin r)
    (hle : (zxP p A hA Γ Φ hw le).eval (ssValue Γ e ^ p) ≠ 0)
    (cinf : Fin r) (hcinf : (zxP p A hA Γ Φ hw cinf).coeff (mAnnuli p) ≠ 0) :
    ∃ i j, zeroChart_nodeRow p A hA Γ Φ hw e le i
        * ((zxP p A hA Γ Φ hw j).coeff (mAnnuli p) * ((zxP p A hA Γ Φ hw cinf).coeff (mAnnuli p))⁻¹)
      ≠ zeroChart_nodeRow p A hA Γ Φ hw e le j
        * ((zxP p A hA Γ Φ hw i).coeff (mAnnuli p) * ((zxP p A hA Γ Φ hw cinf).coeff (mAnnuli p))⁻¹) := by
  obtain ⟨cc, hc⟩ := exists_coeffs p A hA Γ Φ hw 1 (by rw [natDegree_one]; exact Nat.zero_le _)
  obtain ⟨ee, he⟩ := exists_coeffs p A hA Γ Φ hw (X ^ mAnnuli p) (by rw [natDegree_X_pow])
  exact nodeRow_sep_infty Γ (zxP p A hA Γ Φ hw) (one_le_mAnnuli hp5) cc ee hc he e le hle cinf hcinf

theorem zeroChart_residue_goodFamilyZero_linearIndependent :
    LinearIndependent (ResidueField ↥A)
      (fun i => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, zxHint p A hA Γ Φ hw i⟩) :=
  linearIndependent_res _ (zxP p A hA Γ Φ hw) (ssSharp Γ) (ssSharp_ne_zero Γ) (zx_hres p A hA Γ Φ hw)
    (zxP_spec p A hA Γ Φ hw).2.1

end D3
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

end P2MZX5MC
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

namespace P2MZX5A

p2m_open "AlgebraicCurve ModularCurve~jBar Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5 P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5H"

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] [DecidableEq (RatFunc k)]

noncomputable def nodePoly {m : ℕ} (a : Fin m → k) : k[X] := ∏ e : Fin m, (X - C (a e))

theorem nodePoly_ne_zero {m : ℕ} (a : Fin m → k) : nodePoly a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => X_sub_C_ne_zero _

theorem natDegree_nodePoly {m : ℕ} (a : Fin m → k) : (nodePoly a).natDegree = m := by
  unfold nodePoly
  rw [natDegree_prod_of_monic _ _ (fun e _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem prod_image_eq_aeval_nodePoly {m : ℕ} (a : Fin m → k) (ha : Function.Injective a) :
    (∏ b ∈ Finset.image a Finset.univ, (jB k - algebraMap k ↥(modularFunctionFieldC k 1) b))
      = aeval (jB k) (nodePoly a) := by
  rw [Finset.prod_image (fun x _ y _ h => ha h), nodePoly, _root_.map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem aeval_jB_injective : Function.Injective (aeval (jB k) : k[X] → ↥(modularFunctionFieldC k 1)) := by
  intro Q Q' h
  have : aeval (jB k) (Q - Q') = 0 := by rw [Polynomial.aeval_sub, h, sub_self]
  by_contra hne
  exact aeval_jB_ne_zero k _ (sub_ne_zero.mpr hne) this

theorem exists_poly_of_orders {m : ℕ} (a : Fin m → k) (ha : Function.Injective a) (φ : ↥(modularFunctionFieldC k 1))
    (hnode : ∀ e, -1 ≤ (charLGeomPlaceOfPoint k (a e)).ord φ)
    (hreg : ∀ b : k, (∀ e, b ≠ a e) → 0 ≤ (charLGeomPlaceOfPoint k b).ord φ)
    (hinf : 0 ≤ (vInf k).ord φ) :
    ∃ Q : k[X], Q.natDegree ≤ m ∧ φ * aeval (jB k) (nodePoly a) = aeval (jB k) Q := by
  obtain ⟨Q, hQdeg, hQ⟩ := ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
    (Finset.image a Finset.univ) 0 φ
    (fun b hb => hreg b (fun e he => hb (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he.symm⟩)))
    (fun b hb => by
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hb
      exact hnode e)
    (by simpa using hinf)
  refine ⟨Q, ?_, ?_⟩
  · by_cases hQ0 : Q = 0
    · rw [hQ0, natDegree_zero]; exact Nat.zero_le _
    · have := hQdeg hQ0
      rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin, zero_add] at this
      exact this
  · rw [mul_comm, ← prod_image_eq_aeval_nodePoly a ha]
    exact hQ

theorem mem_degreeLT_succ_of_natDegree_le {Q : k[X]} {m : ℕ} (h : Q.natDegree ≤ m) :
    Q ∈ Polynomial.degreeLT k (m + 1) :=
  Polynomial.mem_degreeLT.mpr ((Polynomial.degree_le_of_natDegree_le h).trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m)))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem exists_smith_block {m : ℕ} (a : Fin m → k) (ha : Function.Injective a)
    {r : ℕ} (hr : r = m + 1) (f : Fin r → ↥(modularFunctionFieldC k 1))
    (hnode : ∀ e l, -1 ≤ (charLGeomPlaceOfPoint k (a e)).ord (f l))
    (hreg : ∀ (b : k) l, (∀ e, b ≠ a e) → 0 ≤ (charLGeomPlaceOfPoint k b).ord (f l))
    (hinf : ∀ l, 0 ≤ (vInf k).ord (f l))
    (hLI : LinearIndependent k f)
    (hf0 : ∀ l : Fin r, (l : ℕ) = 0 → f l = 1) :
    ∃ P : Fin r → k[X],
      (∀ l, (P l).natDegree ≤ m) ∧
      LinearIndependent k P ∧
      (∀ Q : k[X], Q.natDegree ≤ m → Q ∈ Submodule.span k (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 → P l = nodePoly a) ∧
      ∀ l, f l * aeval (jB k) (nodePoly a) = aeval (jB k) (P l) := by
  classical
  choose P hPdeg hP using fun l => exists_poly_of_orders a ha (f l) (fun e => hnode e l) (fun b hb => hreg b l hb) (hinf l)
  have hS := aeval_jB_ne_zero k _ (nodePoly_ne_zero a)

  have hLIP : LinearIndependent k P := by
    rw [linearIndependent_iff'] at hLI ⊢
    intro s g hsum i hi
    have h1 : aeval (jB k) (∑ j ∈ s, g j • P j) = 0 := by rw [hsum, map_zero]
    have h2 : (∑ j ∈ s, g j • f j) * aeval (jB k) (nodePoly a) = 0 := by
      rw [Finset.sum_mul]
      have : ∑ j ∈ s, g j • f j * aeval (jB k) (nodePoly a) = aeval (jB k) (∑ j ∈ s, g j • P j) := by
        rw [_root_.map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, hP j]
        exact (map_smul (aeval (jB k)) (g j) (P j)).symm
      rw [this, h1]
    have h3 : ∑ j ∈ s, g j • f j = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hS
    exact hLI s g h3 i hi
  refine ⟨P, hPdeg, hLIP, ?_, ?_, hP⟩
  ·
    intro Q hQ
    have hmem : ∀ l, P l ∈ Polynomial.degreeLT k (m + 1) := fun l => mem_degreeLT_succ_of_natDegree_le (hPdeg l)
    let P' : Fin r → ↥(Polynomial.degreeLT k (m + 1)) := fun l => ⟨P l, hmem l⟩
    have hLI' : LinearIndependent k P' := by
      apply LinearIndependent.of_comp (Polynomial.degreeLT k (m + 1)).subtype
      exact hLIP
    have hcard : Fintype.card (Fin r) = Module.finrank k ↥(Polynomial.degreeLT k (m + 1)) := by
      rw [Fintype.card_fin, (Polynomial.degreeLTEquiv k (m + 1)).finrank_eq, Module.finrank_fin_fun, hr]
    haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
    have htop : Submodule.span k (Set.range P') = ⊤ := hLI'.span_eq_top_of_card_eq_finrank hcard
    have hQmem : (⟨Q, mem_degreeLT_succ_of_natDegree_le hQ⟩ : ↥(Polynomial.degreeLT k (m + 1)))
        ∈ Submodule.span k (Set.range P') := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hQmem
    have hc' : ∑ i, c i • P i = Q := by
      have h := congrArg Subtype.val hc
      rw [Submodule.coe_sum] at h
      simpa only [Submodule.coe_smul] using h
    exact (Submodule.mem_span_range_iff_exists_fun k).mpr ⟨c, hc'⟩
  ·
    intro l hl
    apply aeval_jB_injective
    rw [← hP l, hf0 l hl, one_mul]

end P2MZX5A
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

namespace P2MZX5MC

p2m_open "AlgebraicCurve ModularCurve~jBar ModularCurve.MultCovering Polynomial IsLocalRing P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5 P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5H P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5A"

section Dock
variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [DecidableEq (ResidueField ↥A)] [DecidableEq (RatFunc (ResidueField ↥A))] [CharP (ResidueField ↥A) p]
  (Γ : ChartCtx p A)

theorem vInf_not_mem_zeroChart_nodes : vInf (ResidueField ↥A) ∉ (zeroChart Γ).nodes := by
  intro hmem
  obtain ⟨a, -, hax⟩ := (mem_zeroChart_nodes_iff' Γ _).mp hmem
  have h1 : (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord (aeval (jB (ResidueField ↥A)) (X - C a)) = 1 := by
    rw [ord_charLGeomPlaceOfPoint_aeval _ a _ (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C_self]
    rfl
  have h2 : (vInf (ResidueField ↥A)).ord (aeval (jB (ResidueField ↥A)) (X - C a)) = -1 := by
    rw [ord_vInf_aeval _ _ (X_sub_C_ne_zero a), natDegree_X_sub_C]
    rfl
  rw [hax] at h1
  rw [h1] at h2
  exact absurd h2 (by norm_num)

theorem ne_pow_of_not_mem_nodes {b : ResidueField ↥A}
    (hb : charLGeomPlaceOfPoint (ResidueField ↥A) b ∉ (zeroChart Γ).nodes) (e : Fin (mAnnuli p)) :
    b ≠ ssValue Γ e ^ p := by
  rintro rfl
  apply hb
  rw [mem_zeroChart_nodes_iff']
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact ⟨ssValue Γ e ^ p, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p (ssValue Γ e)).mpr (ssValue_mem_ssJSet Γ e), rfl⟩

theorem not_mem_nodes_of_forall_ne {b : ResidueField ↥A} (hb : ∀ e : Fin (mAnnuli p), b ≠ ssValue Γ e ^ p) :
    charLGeomPlaceOfPoint (ResidueField ↥A) b ∉ (zeroChart Γ).nodes := by
  intro hmem
  obtain ⟨a, ha, hax⟩ := (mem_zeroChart_nodes_iff' Γ _).mp hmem
  have hab : a = b := charLGeomPlaceOfPoint_injective (ResidueField ↥A) hax
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  have hap : a ^ p ∈ ssJSet p (ResidueField ↥A) := (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p a).mpr ha
  obtain ⟨e, he⟩ := exists_ssValue_eq Γ (a ^ p) hap
  apply hb e
  rw [he, ← pow_mul, ← sq, Γ.supply.pow_sq_eq_self_of_mem a ha, hab]

theorem zeroChart_smith_of_orders {r : ℕ} (D : FamData p r) (hr : r = mAnnuli p + 1)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers)
    (hZ2 : ∀ (e : Fin (mAnnuli p)) (l : Fin r),
      -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩))
    (hZ3 : ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩))
    (hZ5 : LinearIndependent (ResidueField ↥A) (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩))
    (h0 : ∀ l : Fin r, (l : ℕ) = 0 → (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ = 1) :
    ∃ P : Fin r → Polynomial (ResidueField ↥A),
      (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
      LinearIndependent (ResidueField ↥A) P ∧
      (∀ Q : Polynomial (ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
        Q ∈ Submodule.span (ResidueField ↥A) (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 →
        P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ * ssPolyBarZero Γ
        = Polynomial.aeval (jBar (ResidueField ↥A)) (P l) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := exists_smith_block (fun e => ssValue Γ e ^ p) (ssValue_pow_injective Γ) hr
    (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩)
    (fun e l => hZ2 e l)
    (fun b l hb => hZ3 l _ (not_mem_nodes_of_forall_ne p A Γ hb))
    (fun l => hZ3 l _ (vInf_not_mem_zeroChart_nodes p A Γ))
    hZ5 h0
  refine ⟨P, h1, h2, h3, h4, fun l => ?_⟩
  rw [ssPolyBarZero_eq_aeval]
  exact h5 l

end Dock
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

end P2MZX5MC
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

namespace P2MZX5MC

p2m_open "AlgebraicCurve ModularCurve~jBar ModularCurve.MultCovering Polynomial IsLocalRing"

theorem residue_goodFamilyZero_eq_one {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (D : FamData p r) (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hexp0 : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp D l = 0)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ l : Fin r, (l : ℕ) = 0 → (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ = 1 := by
  intro l hl
  have h1 : goodFamilyZero D l = 1 := by
    unfold goodFamilyZero
    rw [hexp0 l hl, hzero l hl, pow_zero, map_one, inv_one]
    exact one_mul _
  have h2 : (⟨goodFamilyZero D l, hint l⟩ : (zeroChart Γ).integers) = 1 := Subtype.ext h1
  rw [h2, map_one]

end P2MZX5MC
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth.P2MZX5C"

p2m_open "ModularCurve~jBar" in open AlgebraicCurve IsLocalRing ModularCurve.MultCovering in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (D : FamData p r)
    (hzero  : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hexp0 : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp D l = 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers)
      (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
      (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
      LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
      (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
        Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 →
        P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ * ssPolyBarZero Γ
        = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := by
  classical
  have hint := FamData.goodFamilyZero_mem_zeroChart_integers p D hbasis horthZero A hA Γ
  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 D.t hbasis
  have hle1 := FamData.hasseExp_le_one_of_orth p hp5 D hzero hbasis horthInf horthZero A hA Γ Δ hw1
  exact ⟨hint, P2MZX5MC.zeroChart_smith_of_orders p A Γ D hr hint
    (FamData.neg_one_le_ord_nodeSrc_residue_goodFamilyZero p D hbasis horthInf horthZero hle1 A hA Γ Δ hint)
    (FamData.residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p D hbasis horthZero A hA Γ hint)
    (FamData.linearIndependent_zeroChart_residue_goodFamilyZero p D horthZero A hA Γ hint)
    (P2MZX5MC.residue_goodFamilyZero_eq_one Γ D hzero hexp0 hint)⟩

end S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth
end P2MW
export P2MW.S_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth (solution)
