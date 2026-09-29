-- Prove2me | solution 1 for ModularCurve.exists_ssAnnulus_centred_of_widthOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8f8f489c-a3dd-5656-9405-ab08d5cba415

import Mathlib
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_ord_nodeCoord_sub_eq_one_of_centred
import Theorems.Thm_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.deg Annulus GaussReduction.ord_nonneg_of_mem_gen GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero Place.evalAt_eq_of_hasValue Place.hasValue_evalAt Place.isRational_of_deg_eq_one"
p2m_open "AlgebraicCurve"

open IsLocalRing

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv algebraMap_mem' toValuationSubring HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective evalAt_mul_of_mem IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_eq_of_hasValue hasValue_evalAt isRational_of_deg_eq_one"
p2m_open "AlgebraicCurve.Place"

theorem evalAt_zero_of_isRational {L F : Type*} [Field L] [Field F] [Algebra L F]
    (v : Place L F) (hv : v.IsRational) : v.evalAt (0 : F) = 0 := by
  have h0 : (0 : F) ∈ v.toValuationSubring := zero_mem _
  have h := v.algebraMap_evalAt hv h0
  rw [show (⟨0, h0⟩ : v.toValuationSubring) = 0 from rfl, map_zero] at h
  exact (algebraMap L v.ResidueField).injective (h.trans (map_zero _).symm)

end Place

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

private theorem _root_.AlgebraicCurve.Annulus.param_ne_zero_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param ≠ 0 := by
  obtain ⟨hrat, -, -, hne, -⟩ := An.mem_dom P hP
  intro h0
  rw [h0] at hne
  exact hne (Place.evalAt_zero_of_isRational P hrat)

p2m_export "AlgebraicCurve.Annulus" "param_ne_zero_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.ord_param_eq_zero_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord An.param = 0 := by
  obtain ⟨-, hreg, -, hne, -⟩ := An.mem_dom P hP
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  have hnn : 0 ≤ P.ord An.param := GaussReduction.ord_nonneg_of_mem_gen P hreg h0
  rcases hnn.lt_or_eq with hlt | heq
  · exact absurd (StandardAnnulus.evalAt_eq_zero_of_ord_pos P h0 hlt) hne
  · exact heq.symm

p2m_export "AlgebraicCurve.Annulus" "ord_param_eq_zero_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.inv_param_mem_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param⁻¹ ∈ P.toValuationSubring := by
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  refine GaussReduction.mem_of_ord_nonneg_gen P (inv_ne_zero h0) ?_
  rw [P.ord_inv, An.ord_param_eq_zero_of_mem_dom hP]
  omega

p2m_export "AlgebraicCurve.Annulus" "inv_param_mem_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.evalAt_modulus_mul_param_inv (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)
      = (An.modulus : L) * (P.evalAt An.param)⁻¹ := by
  obtain ⟨hrat, -, -, -, -⟩ := An.mem_dom P hP
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  have hord := An.ord_param_eq_zero_of_mem_dom hP
  rw [GaussReduction.evalAt_mul_of_mem P hrat (P.algebraMap_mem' _)
      (An.inv_param_mem_of_mem_dom hP),
    GaussReduction.evalAt_algebraMap_const P hrat,
    StandardAnnulus.evalAt_inv_of_ord_eq_zero P hrat h0 hord]

p2m_export "AlgebraicCurve.Annulus" "evalAt_modulus_mul_param_inv"

private def _root_.AlgebraicCurve.Annulus.opposite (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) : Annulus A F where
  dom := An.dom
  param := algebraMap L F ((An.modulus : L)) * An.param⁻¹
  modulus := An.modulus
  modulus_mem := An.modulus_mem
  mem_dom := by
    intro P hP
    obtain ⟨hrat, -, ⟨hmemA, hm𝔪⟩, hne, m, hm, hprod⟩ := An.mem_dom P hP
    have hev : P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)
        = (An.modulus : L) * (P.evalAt An.param)⁻¹ := An.evalAt_modulus_mul_param_inv hP
    have hm0 : (m : L) ≠ 0 := by
      intro h0
      exact hπ (by rw [hprod, h0, mul_zero])
    have hevm : P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹) = (m : L) := by
      rw [hev, hprod]
      field_simp
    refine ⟨hrat, mul_mem (P.algebraMap_mem' _) (An.inv_param_mem_of_mem_dom hP), ?_, ?_, ?_⟩
    · rw [hevm]
      exact ⟨m.2, by simpa using hm⟩
    · rw [hevm]
      exact hm0
    · refine ⟨⟨P.evalAt An.param, hmemA⟩, hm𝔪, ?_⟩
      rw [hevm, hprod]
      ring
  existsUnique_evalAt_eq := by
    intro c hc hc0 hadm
    obtain ⟨d, hd, hcd⟩ := hadm
    have hd0 : (d : L) ≠ 0 := by
      intro h0
      exact hπ (by rw [hcd, h0, mul_zero])
    obtain ⟨P, ⟨hPdom, hPeval⟩, huniq⟩ :=
      An.existsUnique_evalAt_eq d hd hd0 ⟨c, hc, by rw [hcd]; ring⟩
    refine ⟨P, ⟨hPdom, ?_⟩, ?_⟩
    · rw [An.evalAt_modulus_mul_param_inv hPdom, hPeval, hcd]
      field_simp
    · rintro Q ⟨hQdom, hQeval⟩
      apply huniq
      refine ⟨hQdom, ?_⟩
      obtain ⟨-, -, -, htQ, -⟩ := An.mem_dom Q hQdom
      rw [An.evalAt_modulus_mul_param_inv hQdom, ← div_eq_mul_inv, div_eq_iff htQ] at hQeval
      rw [hcd] at hQeval
      exact mul_left_cancel₀ hc0 hQeval.symm
  ord_param_sub := by
    intro P hP
    obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
    have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
    have hord := An.ord_param_eq_zero_of_mem_dom hP
    have hev := An.evalAt_modulus_mul_param_inv hP
    rw [hev]
    have hbF : algebraMap L F (P.evalAt An.param) ≠ 0 := (map_ne_zero _).mpr hne
    have hsub : An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
      intro hz0
      have h1 := An.ord_param_sub P hP
      rw [hz0, P.ord_zero] at h1
      exact one_ne_zero h1.symm
    have hfact : algebraMap L F ((An.modulus : L)) * An.param⁻¹
          - algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹)
        = algebraMap L F (-((An.modulus : L) * (P.evalAt An.param)⁻¹))
            * (An.param - algebraMap L F (P.evalAt An.param)) * An.param⁻¹ := by
      simp only [map_neg, map_mul, map_inv₀]
      field_simp
      ring
    rw [hfact]
    have hA1 : algebraMap L F (-((An.modulus : L) * (P.evalAt An.param)⁻¹)) ≠ 0 :=
      (map_ne_zero _).mpr (neg_ne_zero.mpr (mul_ne_zero hπ (inv_ne_zero (fun h =>
        hne h))))
    rw [P.ord_mul (mul_ne_zero hA1 hsub) (inv_ne_zero h0), P.ord_mul hA1 hsub,
      StandardAnnulus.ord_algebraMap_eq_zero P
        (neg_ne_zero.mpr (mul_ne_zero hπ (inv_ne_zero (fun h => hne h)))),
      An.ord_param_sub P hP, P.ord_inv, hord]
    omega
  unit_principle := by
    intro f hf0 hords
    obtain ⟨m, c, hc0, hP⟩ := An.unit_principle f hf0 hords
    refine ⟨-m, c * (An.modulus : L) ^ m, mul_ne_zero hc0 (zpow_ne_zero m hπ), ?_⟩
    intro P hP'
    obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP'
    obtain ⟨hwit, hunit⟩ := hP P hP'
    have hev := An.evalAt_modulus_mul_param_inv hP'
    have e1 : ((An.modulus : L) * (P.evalAt An.param)⁻¹) ^ m
        = (An.modulus : L) ^ m * (P.evalAt An.param) ^ (-m) := by
      rw [mul_zpow, inv_zpow, ← zpow_neg]
    have hkey : P.evalAt f * (c * (An.modulus : L) ^ m)⁻¹
          * (P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)) ^ (-(-m))
        = P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) := by
      rw [hev, neg_neg, e1, mul_inv,
        show P.evalAt f * (c⁻¹ * ((An.modulus : L) ^ m)⁻¹)
            * ((An.modulus : L) ^ m * (P.evalAt An.param) ^ (-m))
          = P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m)
              * (((An.modulus : L) ^ m)⁻¹ * (An.modulus : L) ^ m) from by ring,
        inv_mul_cancel₀ (zpow_ne_zero m hπ), mul_one]
    rw [hkey]
    exact ⟨hwit, hunit⟩

p2m_export "AlgebraicCurve.Annulus" "opposite"

theorem opposite_dom (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).dom = An.dom := rfl

theorem opposite_modulus (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).modulus = An.modulus := rfl

theorem opposite_param (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).param = algebraMap L F ((An.modulus : L)) * An.param⁻¹ := rfl

theorem opposite_param_mul (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0)
    (hz : An.param ≠ 0) :
    (An.opposite hπ).param * An.param = algebraMap L F ((An.modulus : L)) := by
  rw [opposite_param, mul_assoc, inv_mul_cancel₀ hz, mul_one]

theorem opposite_pair_spec (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0)
    (hz : An.param ≠ 0) :
    (An.opposite hπ).dom = An.dom ∧ (An.opposite hπ).modulus = An.modulus ∧
      (((An.modulus : L)) ≠ 0) ∧
      (An.opposite hπ).param * An.param = algebraMap L F ((An.modulus : L)) :=
  ⟨rfl, rfl, hπ, opposite_param_mul An hπ hz⟩

end Annulus

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.exists_hasValue_nodeCoord_of_centred deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
p2m_open "ModularCurve~coeffEmb_jq"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve IsLocalRing"

variable {q : ℕ} [Fact q.Prime] [NeZero (1 * q)] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]

def jEltBar (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

def jqEltBar (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

def ssNodeCoord (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  jqEltBar q - jEltBar q ^ q

def IsCentredAt (red : A →+* k) (a : k)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  (∃ x : A, red x = a ∧
    0 < W.ord (jEltBar q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : A, red y = a ^ q ∧
    0 < W.ord (jqEltBar q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))

section Bridges

private theorem _root_.AlgebraicCurve.Place.evalAt_eq_of_hasValue {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F} {a : L} (h : v.HasValue g a) :
    v.evalAt g = a := by
  obtain ⟨hm, hres⟩ := h
  have h1 := v.algebraMap_evalAt hv hm
  exact (algebraMap L v.ResidueField).injective (h1.trans hres)

p2m_alias "P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve.Place.evalAt_eq_of_hasValue" "AlgebraicCurve.Place.evalAt_eq_of_hasValue"

private theorem _root_.AlgebraicCurve.Place.hasValue_evalAt {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F}
    (hm : g ∈ v.toValuationSubring) : v.HasValue g (v.evalAt g) :=
  ⟨hm, (v.algebraMap_evalAt hv hm).symm⟩

p2m_alias "P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve.Place.hasValue_evalAt" "AlgebraicCurve.Place.hasValue_evalAt"

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one {L F : Type*} [Field L] [Field F]
    [Algebra L F] (v : Place L F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve.Place.isRational_of_deg_eq_one" "AlgebraicCurve.Place.isRational_of_deg_eq_one"

theorem isRational_place_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.IsRational :=
  w.isRational_of_deg_eq_one (deg_eq_one_modularFunctionFieldBar M w)

omit [Fact (Nat.Prime q)] [NeZero (1 * q)] [IsAlgClosed k] [DecidableEq k] in

theorem natCast_mem_maximalIdeal_of_charP (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
  (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)

end Bridges

section Transport

variable (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
variable (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ q ^ 2 = a)
variable (h0 : a ≠ 0) (h1728 : a ≠ 1728)

set_option maxHeartbeats 12800000 in

def ssAnnulus
    (h_unit : ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
      (∀ W, IsCentredAt red a W → W.ord f = 0) →
      ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
        ∀ W, IsCentredAt red a W →
          ∃ h : W.evalAt f * c⁻¹ * (W.evalAt (ssNodeCoord q)) ^ (-m) ∈ A,
            IsUnit (⟨_, h⟩ : A)) :
    Annulus A ↥(modularFunctionFieldBar (1 * q)) where
  dom := {W | IsCentredAt red a W}
  param := ssNodeCoord q
  modulus := ((q : ℕ) : A)
  modulus_mem := natCast_mem_maximalIdeal_of_charP red hker
  mem_dom := by
    intro W hW
    obtain ⟨c, hcm, ⟨d, hdm, hcd⟩, hGc⟩ :=
      ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2
        h0 h1728 W hW
    have hrat : W.IsRational := isRational_place_modularFunctionFieldBar (1 * q) W
    have hqA : (((q : ℕ) : A) : AlgebraicClosure ℚ) ≠ 0 := by
      have : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
      simpa using this
    have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0c
      apply hqA
      rw [← hcd]
      push_cast
      rw [h0c, zero_mul]
    have hev : W.evalAt (ssNodeCoord q) = (c : AlgebraicClosure ℚ) :=
      Place.evalAt_eq_of_hasValue hrat hGc
    refine ⟨hrat, hGc.mem, ?_, ?_, ?_⟩
    · rw [hev]
      exact ⟨c.2, by simpa using hcm⟩
    · rw [hev]
      exact hc0
    · refine ⟨d, hdm, ?_⟩
      rw [hev]
      exact_mod_cast hcd.symm
  existsUnique_evalAt_eq := by
    intro c hc hc0 hadm
    obtain ⟨m, hmm, hqm⟩ := hadm
    have hcd : c * m = ((q : ℕ) : A) := by
      apply Subtype.coe_injective
      push_cast
      exact hqm.symm
    obtain ⟨W, ⟨hWc, hWval⟩, huniq⟩ :=
      ModularCurve.NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord red hker hq a
        ha ha2 h0 h1728 c hc ⟨m, hmm, hcd⟩
    refine ⟨W, ⟨hWc, Place.evalAt_eq_of_hasValue
      (isRational_place_modularFunctionFieldBar (1 * q) W) hWval⟩, ?_⟩
    rintro V ⟨hVc, hVev⟩
    apply huniq
    refine ⟨hVc, ?_⟩
    obtain ⟨c', -, -, hGc'⟩ :=
      ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2
        h0 h1728 V hVc
    have h2 : V.HasValue (ssNodeCoord q) (V.evalAt (ssNodeCoord q)) :=
      Place.hasValue_evalAt (isRational_place_modularFunctionFieldBar (1 * q) V) hGc'.mem
    rw [hVev] at h2
    exact h2
  ord_param_sub := by
    intro W hW
    obtain ⟨c, -, -, hGc⟩ :=
      ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2
        h0 h1728 W hW
    have hev : W.evalAt (ssNodeCoord q) = (c : AlgebraicClosure ℚ) :=
      Place.evalAt_eq_of_hasValue (isRational_place_modularFunctionFieldBar (1 * q) W) hGc
    rw [hev]
    exact ModularCurve.NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred red hker hq a ha ha2
      h0 h1728 W hW c hGc
  unit_principle := by
    intro f hf0 hord
    obtain ⟨m, c, hc0, hP⟩ := h_unit f hf0 (fun W hW => hord W hW)
    exact ⟨m, c, hc0, fun W hW => hP W hW⟩

variable (h_unit : ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
      (∀ W, IsCentredAt red a W → W.ord f = 0) →
      ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
        ∀ W, IsCentredAt red a W →
          ∃ h : W.evalAt f * c⁻¹ * (W.evalAt (ssNodeCoord q)) ^ (-m) ∈ A,
            IsUnit (⟨_, h⟩ : A))

theorem ssAnnulus_dom :
    (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).dom = {W | IsCentredAt red a W} := rfl

theorem ssAnnulus_param :
    (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).param = ssNodeCoord q := rfl

theorem ssAnnulus_modulus :
    (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus = ((q : ℕ) : A) := rfl

theorem ssAnnulus_modulus_ne_zero :
    (((ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus : AlgebraicClosure ℚ)) ≠ 0 := by
  have h : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  simpa [ssAnnulus_modulus] using h

def ssAnnulusOpp : Annulus A ↥(modularFunctionFieldBar (1 * q)) :=
  (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).opposite
    (ssAnnulus_modulus_ne_zero red hker hq a ha ha2 h0 h1728 h_unit)

theorem ssAnnulus_pair {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : W ∈ (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).dom) :
    (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).dom
        = (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).dom ∧
      (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).modulus
        = (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus ∧
      (((ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).param
          * (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
            (((ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus : AlgebraicClosure ℚ)) :=
  Annulus.opposite_pair_spec _
    (ssAnnulus_modulus_ne_zero red hker hq a ha ha2 h0 h1728 h_unit)
    (Annulus.param_ne_zero_of_mem_dom _ hW)

omit [NeZero (1 * q)] [IsAlgClosed k] [DecidableEq k] in
include red hker in

theorem exists_admissible_value :
    ∃ c : A, c ∈ IsLocalRing.maximalIdeal A ∧ (c : AlgebraicClosure ℚ) ≠ 0 ∧
      ∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ)
    (n := 2) (by norm_num)
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hs0 : s ≠ 0 := by
    intro h
    apply hq0
    rw [← hs, h]
    ring
  have hqm : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    natCast_mem_maximalIdeal_of_charP red hker
  rcases A.mem_or_inv_mem s with hsA | hsiA
  · have hprime : (IsLocalRing.maximalIdeal A).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime
    have hsq : (⟨s, hsA⟩ : A) ^ 2 = ((q : ℕ) : A) := by
      apply Subtype.coe_injective
      push_cast
      exact hs
    have hmem : (⟨s, hsA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      hprime.mem_of_pow_mem 2 (by rw [hsq]; exact hqm)
    exact ⟨⟨s, hsA⟩, hmem, hs0, ⟨s, hsA⟩, hmem, by rw [← hsq, sq]⟩
  · exfalso
    have hq1 : ((q : ℕ) : AlgebraicClosure ℚ) * (s⁻¹) ^ 2 = 1 := by
      rw [inv_pow, hs]
      exact mul_inv_cancel₀ hq0
    have h1A : ((q : ℕ) : A) * (⟨s⁻¹, hsiA⟩ : A) ^ 2 = 1 := by
      apply Subtype.coe_injective
      push_cast
      exact hq1
    have h1m : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← h1A]
      exact Ideal.mul_mem_right _ _ hqm
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1m)

theorem exists_mem_dom_ssAnnulus :
    ∃ W, W ∈ (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).dom := by
  obtain ⟨c, hcm, -, d, hdm, hcd⟩ := exists_admissible_value (q := q) (A := A) red hker
  obtain ⟨W, ⟨hWc, -⟩, -⟩ :=
    ModularCurve.NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord red hker hq a
      ha ha2 h0 h1728 c hcm ⟨d, hdm, hcd⟩
  exact ⟨W, hWc⟩

theorem ssAnnulus_pair' :
    (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).dom
        = (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).dom ∧
      (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).modulus
        = (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus ∧
      (((ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      (ssAnnulusOpp red hker hq a ha ha2 h0 h1728 h_unit).param
          * (ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
            (((ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit).modulus : AlgebraicClosure ℚ)) := by
  obtain ⟨W, hW⟩ := exists_mem_dom_ssAnnulus red hker hq a ha ha2 h0 h1728 h_unit
  exact ssAnnulus_pair red hker hq a ha ha2 h0 h1728 h_unit hW

end Transport

end ModularCurve

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.exists_hasValue_nodeCoord_of_centred deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom"
p2m_open "ModularCurve.CharPReduction ModularCurve~coeffEmb_jq"

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_congr {x y : LaurentSeries L} (hxy : x = y)
    (h : ∃ hx : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    ∃ hy : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, hy⟩ ≠ 0 := by
  subst hxy
  exact h

theorem gaussUnit_one :
    ∃ h : (1 : LaurentSeries L) ∈ modularLocalized N A red, modularRedLocHom N A red ⟨1, h⟩ ≠ 0 := by
  refine ⟨one_mem _, ?_⟩
  have h1 : (⟨1, one_mem _⟩ : modularLocalized N A red) = 1 := rfl
  rw [h1, map_one]
  exact one_ne_zero

theorem gaussUnit_mul {x y : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0)
    (hy : ∃ h : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, h⟩ ≠ 0) :
    ∃ h : x * y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x * y, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨hy, hy0⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have hxy : (⟨x * y, mul_mem hx hy⟩ : modularLocalized N A red) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hxy, map_mul]
  exact mul_ne_zero hx0 hy0

theorem gaussUnit_inv {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨r, s, hs, hxs⟩ :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mp hx
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  have hspec := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ hxs
  have hx0' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ ≠ 0 := hx0
  have hrne : redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hx0' hsne
  have hr : r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    (notMem_redKer_iff A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr hrne
  have hxne : x ≠ 0 := by
    intro hx0
    apply hrne
    have hr0 : r = 0 := by
      apply Subtype.ext
      rw [← hxs, hx0, zero_mul]
      rfl
    rw [hr0, map_zero]
  have hinv : x⁻¹ * r = s := by
    rw [← hxs, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
  have hmem : x⁻¹ ∈ modularLocalized N A red :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr ⟨s, r, hr, hinv⟩
  refine ⟨hmem, ?_⟩
  have hspec' := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ hinv
  intro hzero
  apply hsne
  have hzero' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ = 0 := hzero
  rw [← hspec', hzero', zero_mul]

theorem gaussUnit_pow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℕ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact gaussUnit_one N A red
  | succ n ih =>
      rw [pow_succ]
      exact gaussUnit_mul N A red ih hx

theorem gaussUnit_zpow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℤ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact gaussUnit_pow N A red hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact gaussUnit_inv N A red (gaussUnit_pow N A red hx (n + 1))

end ModularCurve.CharPReduction

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.deg Annulus GaussReduction.ord_nonneg_of_mem_gen GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero Place.evalAt_eq_of_hasValue Place.hasValue_evalAt Place.isRational_of_deg_eq_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv algebraMap_mem' toValuationSubring HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective evalAt_mul_of_mem IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_eq_of_hasValue hasValue_evalAt isRational_of_deg_eq_one"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem evalAt_eq_of_hasValue' {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

theorem hasValue_zpow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
      exact hasValue_pow_of_hasValue h n
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc]
      exact (hasValue_pow_of_hasValue h (n + 1)).inv (pow_ne_zero _ ha)

end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.exists_hasValue_nodeCoord_of_centred deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit modularEval exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero ord_nodeCoord_sub_eq_one_of_centred existsUnique_place_centred_hasValue_nodeCoord exists_hasValue_nodeCoord_of_centred"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

theorem isRational_of_level {q : ℕ} [Fact q.Prime] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : V.IsRational :=
  isRational_place_modularFunctionFieldBar (1 * q) V

theorem correction_identity {K : Type*} [Field K] (a c q w : K) (m : ℤ) :
    a * (c⁻¹ * q ^ (-m))⁻¹ * w ^ (-m) = c * a * (q * w⁻¹) ^ m := by
  rw [mul_zpow, inv_zpow', mul_inv, inv_inv, zpow_neg q m, inv_inv]
  ring

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]

theorem frickeInvolutionBar_jqElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
          modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A.toSubring) :
    red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A.toSubring)
      = ((jqModC ℤ).coeff n : ↥A.toSubring) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A.toSubring) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

theorem redRes_jqModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red n _

theorem redRes_jqNModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A.toSubring := CharPReduction.jqModC_mem_integralCoeffs A.toSubring m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    modularEval N A.toSubring P ∈ CharPReduction.modularRing N A.toSubring := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A.toSubring c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A.toSubring
      · exact CharPReduction.jqNModC_mem_modularRing N A.toSubring

theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).comp
      ((modularEval (1 * q) A.toSubring).codRestrict (CharPReduction.modularRing (1 * q) A.toSubring)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨CharPReduction.constSeries A.toSubring c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red ⟨(CharPReduction.constSeries A.toSubring c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A.toSubring c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A.toSubring) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A.toSubring) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

omit [Fact q.Prime] in

theorem eval₂Hom_kroneckerPolynomial (a : k) (R : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval₂Hom red ![a, a ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
  set E : MvPolynomial (Fin 2) ↥A.toSubring →+* k := MvPolynomial.eval₂Hom red ![a, a ^ q] with hE
  set g : Polynomial ℤ →+* MvPolynomial (Fin 2) ↥A.toSubring :=
    Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0) with hg
  have h1 : E (Polynomial.eval₂ g (MvPolynomial.X 1) R) = R.eval₂ (E.comp g) (E (MvPolynomial.X 1)) :=
    Polynomial.hom_eval₂ R g E (MvPolynomial.X 1)
  have hEg : E.comp g = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, hE,
        MvPolynomial.eval₂Hom_C, eq_intCast, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast]
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hE, MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hEX : E (MvPolynomial.X 1) = a ^ q := by
    rw [hE, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [h1, hEg, hEX]

  have h2 : ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a
      = R.eval₂ ((Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k))) (Polynomial.eval a (Polynomial.C (a ^ q))) := by
    rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  have h3 : (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k)) = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [h2, h3, Polynomial.eval_C]

end Red

theorem exists_kroneckerRemainder (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q) :
    ∃ R : Polynomial (Polynomial ℤ),
      data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
        + Polynomial.C (Polynomial.C (q : ℤ)) * R := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hKr : KroneckerCongruence q data := kroneckerCongruence q data
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣
      data.Φ - (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun S : Polynomial (Polynomial (ZMod q)) => (S.coeff n).coeff m) hKr
    have hprod : reduceModBivar q ((Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q))
        = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
      simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
    rw [← hprod] at h
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.coeff_sub, Polynomial.coeff_sub, Int.cast_sub, sub_eq_zero]
    exact h
  obtain ⟨R, hR⟩ := hdvd
  exact ⟨R, by rw [← hR]; ring⟩

section Gauss

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩ ≠ 0) :
    ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0 := by
  refine ⟨CharPReduction.subring_le_localizedAtKer A.toSubring red _ _ hx, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩
  intro h0
  apply hred
  rw [← h]
  exact h0

theorem gaussUnit_of_mem_modularRing_div {r s : LaurentSeries (AlgebraicClosure ℚ)}
    (hr : r ∈ CharPReduction.modularRing (1 * q) A.toSubring) (hs : s ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hrred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r, hr⟩ ≠ 0)
    (hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨s, hs⟩ ≠ 0) :
    ∃ h : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨r * s⁻¹, h⟩ ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    apply hsred
    have : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hnot : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring) (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hsred
  have hpres : r * s⁻¹ * s = r := by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have hmem : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := ⟨⟨r, hr⟩, ⟨s, hs⟩, hnot, hpres⟩
  refine ⟨hmem, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r * s⁻¹, hmem⟩ (r := ⟨r, hr⟩) (s := ⟨s, hs⟩) hpres
  exact left_ne_zero_of_mul (ne_of_eq_of_ne hspec hrred)

theorem gaussData_nodeCoord' [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    (∃ (h₁ : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q))⁻¹ :
            modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) ∧
      (∃ (h₂ : ((frickeInvolutionBar (1 * q) (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) : modularFunctionFieldBar (1 * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨J, hJ⟩ : ∃ J : ↥(modularFunctionFieldBar (1 * q)), J = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := ⟨_, rfl⟩
  obtain ⟨JQ, hJQ⟩ : ∃ JQ : ↥(modularFunctionFieldBar (1 * q)), JQ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := ⟨_, rfl⟩
  rw [← hJ, ← hJQ]
  have hJser : (J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hJ]; exact coeffEmb_jq
  have hJQser : (JQ : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hJQ]; exact coeffEmb_qExpand_jq (1 * q)

  have hGser : ((JQ - J ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hHser : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]

  have hHred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ ≠ 0 := by
    rw [redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      intro h
      have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
      rw [Polynomial.natDegree_X, ← pow_mul, Polynomial.natDegree_X_pow] at hdeg
      have h25 : 25 ≤ q * q := Nat.mul_le_mul hq hq
      rw [← hdeg] at h25
      exact absurd h25 (by norm_num)
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩

  obtain ⟨data⟩ := nonempty_modularPolynomialData q
  obtain ⟨R, hR⟩ := exists_kroneckerRemainder q data
  have hRne := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR a ha h0 h1728
  have hEval := modularEval_kroneckerRemainder A data R hR
  rw [← hJ, ← hJQ] at hEval

  obtain ⟨Rser, hRser⟩ : ∃ Rser : LaurentSeries (AlgebraicClosure ℚ), Rser = modularEval (1 * q) A.toSubring
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring) := ⟨_, rfl⟩
  rw [← hRser] at hEval
  have hRmem : Rser ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hRser]; exact modularEval_mem_modularRing (1 * q) _
  have hRred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨Rser, hRmem⟩ ≠ 0 := by
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = ⟨modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), modularEval_mem_modularRing (1 * q) _⟩ := Subtype.ext hRser
    rw [hx, redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      intro h
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a, h, Polynomial.eval_zero]
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩
  have hHmem : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hHser]; exact modularEval_mem_modularRing (1 * q) _
  have hHred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hHmem⟩ ≠ 0 := by
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring))
        = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ :=
      Subtype.ext hHser
    rw [hx]; exact hHred
  have hH0 : (J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h
    apply hHred'
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 :=
      Subtype.ext (by
        show ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [h]; rfl)
    rw [hx, map_zero]
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  constructor
  ·
    have hident : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
        = (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ := by
      have h : (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
            * ((J - JQ ^ q) * (J - JQ ^ q)⁻¹) := by
        rw [mul_inv, inv_inv, mul_inv]; ring
      rw [h, mul_inv_cancel₀ hH0, mul_one]
    have hcoe : (((J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
      rw [MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul,
        hEval, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_natCast,
        map_natCast, show (((q : ℕ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = (modularFunctionFieldBar (1 * q)).val (q : ↥(modularFunctionFieldBar (1 * q))) from rfl, map_natCast]
    refine CharPReduction.gaussUnit_congr (1 * q) A.toSubring red ((congrArg Subtype.val hident).trans hcoe).symm ?_
    exact gaussUnit_of_mem_modularRing_div red hHmem hRmem hHred' hRred'
  ·
    have hσJ : frickeInvolutionBar (1 * q) J = JQ := by rw [hJ, hJQ]; exact frickeInvolutionBar_jElt q
    have hσJQ : frickeInvolutionBar (1 * q) JQ = J := by rw [hJ, hJQ]; exact frickeInvolutionBar_jqElt q
    have hσG : frickeInvolutionBar (1 * q) (JQ - J ^ q) = J - JQ ^ q := by rw [map_sub, map_pow, hσJ, hσJQ]
    rw [hσG]
    exact gaussUnit_of_mem_modularRing red hHmem hHred'

end Gauss

theorem gaussUnit_corrected {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (c : AlgebraicClosure ℚ) (m : ℤ) (f G : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (h₂ : ∃ h : ((frickeInvolutionBar (1 * q)
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₂ : ∃ h : ((frickeInvolutionBar (1 * q) G : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    (∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) ∧
    (∃ h : ((frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) := by
  have coe_zpow : ∀ (x : ↥(modularFunctionFieldBar (1 * q))) (n : ℤ), ((x ^ n : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ^ n := by
    intro x n
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, IntermediateField.coe_pow]
    | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, IntermediateField.coe_pow]
  constructor
  · rw [MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₁
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₁ m)
  · have hσ : frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m)
        = frickeInvolutionBar (1 * q)
            (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f)
          * (frickeInvolutionBar (1 * q) G) ^ (-m) := by
      simp only [map_mul, map_zpow₀, AlgEquiv.commutes, mul_zpow, inv_zpow']
      ring
    rw [hσ, MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₂
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₂ (-m))

theorem hasValue_corrected {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) {qK : K}
    (hqK : qK ≠ 0) (m : ℤ) {f G : F} {aV cV : K} (hf : v.HasValue f aV) (hG : v.HasValue G cV) (hcV : cV ≠ 0) :
    v.HasValue (algebraMap K F c * f * (algebraMap K F qK * G⁻¹) ^ m) (c * aV * (qK * cV⁻¹) ^ m) :=
  ((v.hasValue_algebraMap c).mul hf).mul
    (Place.hasValue_zpow_of_hasValue ((v.hasValue_algebraMap qK).mul (hG.inv hcV))
      (mul_ne_zero hqK (inv_ne_zero hcV)) m)

theorem exists_hasValue_ne_zero_of_ord_eq_zero {q : ℕ} [Fact q.Prime] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {f : ↥(modularFunctionFieldBar (1 * q))} (hf : f ≠ 0)
    (hord : V.ord f = 0) : ∃ aV : AlgebraicClosure ℚ, aV ≠ 0 ∧ V.HasValue f aV := by
  have hfU := V.exists_isUnit_of_ord_eq_zero hf hord
  obtain ⟨hfmem, hfunit⟩ := hfU
  have hfV := V.exists_hasValue_of_surjective (isRational_of_level V) hfmem
  obtain ⟨aV, haV, haV0⟩ := hfV
  exact ⟨aV, haV0 hfunit, haV⟩

theorem exists_hasValue_nodeCoord_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ cV : AlgebraicClosure ℚ, cV ≠ 0 ∧ V.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) cV := by
  have htrio := exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 V hV
  obtain ⟨cV, -, ⟨d, -, hcd⟩, hGV⟩ := htrio
  have hqA0 : ((q : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  refine ⟨(cV : AlgebraicClosure ℚ), ?_, hGV⟩
  intro hz
  have hcV : cV = 0 := Subtype.ext hz
  apply hqA0
  rw [← hcd, hcV, zero_mul]

theorem exists_int_isUnit_evalAt_of_twoBranchNormalisation_of_maximumPrinciple
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (hJump : ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (m : ℤ)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hMax : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (∃ (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
          CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) →
      (∃ (h₂ : ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (1 * q) A.toSubring red),
          CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0) →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord g = 0) →
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → ∃ h : W.evalAt g ∈ A, IsUnit (⟨_, h⟩ : A)) :
    ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
        ∃ h : W.evalAt f * c⁻¹ * (W.evalAt ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  obtain ⟨c, hc0, m, h₁, h₂, hu₁, hu₂⟩ := hJump
  obtain ⟨hG₁, hG₂⟩ := gaussData_nodeCoord' red hq a ha h0 h1728
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  obtain ⟨Gq, hGq_def⟩ : ∃ Gq : ↥(modularFunctionFieldBar (1 * q)), Gq = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) := ⟨_, rfl⟩
  rw [← hGq_def] at hG₁ hG₂

  have hsm₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    congrArg Subtype.val (Algebra.smul_def c f)
  have hsm₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q)
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    congrArg (fun z : ↥(modularFunctionFieldBar (1 * q)) => ((frickeInvolutionBar (1 * q) z : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))
      (Algebra.smul_def (c * (q : AlgebraicClosure ℚ) ^ m) f)

  have hgauss := gaussUnit_corrected red c m f Gq
    (CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hsm₁ ⟨h₁, hu₁⟩)
    (CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hsm₂ ⟨h₂, hu₂⟩) hG₁ hG₂
  obtain ⟨hg1, hg2⟩ := hgauss
  obtain ⟨g, hg_def⟩ : ∃ g : ↥(modularFunctionFieldBar (1 * q)), g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
      * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * Gq⁻¹) ^ m := ⟨_, rfl⟩
  rw [← hg_def] at hg1 hg2

  refine ⟨m, c⁻¹ * (q : AlgebraicClosure ℚ) ^ (-m), mul_ne_zero (inv_ne_zero hc0) (zpow_ne_zero _ hq0), ?_⟩
  intro W hW
  have hMaxW := hMax g hg1 hg2 (fun V hV => by
    have hGv := exists_hasValue_nodeCoord_ne_zero red hker hq a ha ha2 h0 h1728 V hV
    obtain ⟨cV, hcV0, hGV⟩ := hGv
    rw [← hGq_def] at hGV
    have hfv := exists_hasValue_ne_zero_of_ord_eq_zero V hf (hford V hV)
    obtain ⟨aV, haV0, haV⟩ := hfv
    have hgV := hasValue_corrected V c hq0 m haV hGV hcV0
    rw [← hg_def] at hgV
    exact hgV.ord_eq_zero
      (mul_ne_zero (mul_ne_zero hc0 haV0) (zpow_ne_zero _ (mul_ne_zero hq0 (inv_ne_zero hcV0))))) W hW
  obtain ⟨hA, hunit⟩ := hMaxW
  have hGw := exists_hasValue_nodeCoord_ne_zero red hker hq a ha ha2 h0 h1728 W hW
  obtain ⟨cW, hcW0, hGW⟩ := hGw
  have hfw := exists_hasValue_ne_zero_of_ord_eq_zero W hf (hford W hW)
  obtain ⟨aW, -, haW⟩ := hfw
  have hevalG : W.evalAt (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) = cW := Place.evalAt_eq_of_hasValue' hGW
  rw [← hGq_def] at hGW
  have hgW := hasValue_corrected W c hq0 m haW hGW hcW0
  rw [← hg_def] at hgW
  have hevalf : W.evalAt f = aW := Place.evalAt_eq_of_hasValue' haW
  have hevalg : W.evalAt g = c * aW * ((q : AlgebraicClosure ℚ) * cW⁻¹) ^ m := Place.evalAt_eq_of_hasValue' hgW
  have heq : W.evalAt f * (c⁻¹ * (q : AlgebraicClosure ℚ) ^ (-m))⁻¹ * (W.evalAt (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q))) ^ (-m)
      = W.evalAt g := by
    rw [hevalf, hevalG, hevalg]
    exact correction_identity aW c _ cW m
  rw [heq]
  exact ⟨hA, hunit⟩

theorem maximumPrinciple_nodeTube
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg₁ : ∃ (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (hg₂ : ∃ (h₂ : ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hgord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord g = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ h : W.evalAt g ∈ A, IsUnit (⟨_, h⟩ : A) := by
  obtain ⟨h₁, h₁u⟩ := hg₁
  obtain ⟨h₂, h₂u⟩ := hg₂
  exact isUnit_evalAt_of_forall_centred_ord_eq_zero_of_gaussUnit red hker hq a ha ha2 h0 h1728 g h₁ h₁u h₂ h₂u hgord W hW

theorem exists_int_isUnit_evalAt_of_forall_centred_ord_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) :
    ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
        ∃ h : W.evalAt f * c⁻¹ * (W.evalAt ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A) :=
  exists_int_isUnit_evalAt_of_twoBranchNormalisation_of_maximumPrinciple red hker hq a ha ha2 h0 h1728 f hf hford
    (exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero red hker hq a ha ha2 h0 h1728 f hf hford)
    (fun g hg₁ hg₂ hgord W hW => maximumPrinciple_nodeTube red hker hq a ha ha2 h0 h1728 g hg₁ hg₂ hgord W hW)

end ModularCurve.NodeLocalized

p2m_open "ModularCurve~coeffEmb_jq" in open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne.ModularCurve in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) ∧
      An.param = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q ∧
      An.modulus = ((q : ℕ) : A) := by
  have HU : ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
      (∀ W, ModularCurve.IsCentredAt red a W → W.ord f = 0) →
      ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
        ∀ W, ModularCurve.IsCentredAt red a W →
          ∃ h : W.evalAt f * c⁻¹ * (W.evalAt (ModularCurve.ssNodeCoord q)) ^ (-m) ∈ A,
            IsUnit (⟨_, h⟩ : A) :=
    fun f hf hford =>
      ModularCurve.NodeLocalized.exists_int_isUnit_evalAt_of_forall_centred_ord_eq_zero red hker hq a ha ha2 h0
        h1728 f hf hford
  exact ⟨ModularCurve.ssAnnulus red hker hq a ha ha2 h0 h1728 HU,
    ModularCurve.ssAnnulusOpp red hker hq a ha ha2 h0 h1728 HU,
    ModularCurve.ssAnnulus_pair' red hker hq a ha ha2 h0 h1728 HU, fun W => Iff.rfl, rfl, rfl⟩

end

end S_ModularCurve_exists_ssAnnulus_centred_of_widthOne
end P2MW
export P2MW.S_ModularCurve_exists_ssAnnulus_centred_of_widthOne (solution)
