-- Prove2me | solution 1 for ModularCurve.exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/43763ca2-9f6d-5a99-800a-5075fcff8227

import Mathlib
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes
import Theorems.Thm_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
import Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
import Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.NodeLocalized.coe_modularEvalAt AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"
open ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC qExpand jq jq_mem jqd_mem_full modularFunctionField_le_full ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes frickeInvolutionBar modularFunctionFieldBar exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728 charLGeomPlaceOfPoint isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace WPkgProof
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized"

theorem exists_mul_eq_one_of_redRestrict_ne_zero
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) :
    ∃ d : ↥(coeffSubring A K), c * d = 1 := by
  let cA : A := Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c
  have hcA : cA ∉ IsLocalRing.maximalIdeal A := fun h => hc ((hker cA).mpr h)
  obtain ⟨b, hb⟩ := (IsLocalRing.notMem_maximalIdeal.mp hcA).exists_right_inv
  have hb' : (c : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbinv : (b : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbK : (b : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := by
    rw [hbinv]
    exact K.inv_mem (Subring.mem_inf.mp c.2).2
  refine ⟨⟨(b : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact hb'

theorem exists_uniformizer_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hEq | hDVR
  · exfalso
    have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : (q : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [hEq]
      show (q : AlgebraicClosure ℚ)⁻¹ ∈ K
      exact inv_mem (natCast_mem K q)
    have hcoe : (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) :=
      map_natCast (coeffSubring A K).subtype q
    have hone : ((q : ℕ) : ↥(coeffSubring A K)) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      show (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) * (q : AlgebraicClosure ℚ)⁻¹ = 1
      rw [hcoe, mul_inv_cancel₀ hq0]
    have h := congrArg (redRestrict red K) hone
    rw [map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, map_one] at h
    exact zero_ne_one h
  · haveI := hDVR
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    have hmax : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    refine ⟨ϖ, fun c => ⟨fun hc0 => ?_, ?_⟩⟩
    · have hcm : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨d, hd⟩ := hu.exists_right_inv
        have h := congrArg (redRestrict red K) hd
        rw [map_mul, hc0, zero_mul, map_one] at h
        exact zero_ne_one h
      rw [hmax, Ideal.mem_span_singleton'] at hcm
      obtain ⟨d, hd⟩ := hcm
      exact ⟨d, by rw [← hd, mul_comm]⟩
    · rintro ⟨d, rfl⟩
      rw [map_mul]
      suffices hϖ0 : redRestrict red K ϖ = 0 by rw [hϖ0, zero_mul]
      by_contra hne
      obtain ⟨e, he⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K ϖ hne
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one e he)

theorem ofNat1728_ne_zero {q : ℕ} [Fact q.Prime] (k : Type*) [Field k] [CharP k q] (hq : 5 ≤ q) :
    (1728 : k) ≠ 0 := by
  have hp : q.Prime := Fact.out
  intro h
  have h' : ((1728 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k q] at h'
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [h1728] at h'
  rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

end WPkgProof
end ModularCurve

open AlgebraicCurve IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized in
set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type}
    [Field Fbar0]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    {Fbari : Type}
    [Field Fbari]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodes0 : x0 ∈ C0.nodes)
    (hnodesi : xi ∈ Ci.nodes)
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))
    (huniti : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * p))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      An.IsAttached C0 x0 ∧ An'.IsAttached Ci xi ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ))))) ∧
      An.modulus = ((p : ℕ) : ↥A) ^ jWidth a := by
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c

  obtain ⟨K, hKfd, -, x, hx⟩ :=
    ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A (IsLocalRing.residue ↥A) a
      (IsLocalRing.residue_surjective a) (1 : ↥(modularFunctionFieldBar (1 * p)))
  haveI : FiniteDimensional ℚ K := hKfd
  obtain ⟨ϖ, hϖ⟩ := ModularCurve.WPkgProof.exists_uniformizer_coeffSubring (IsLocalRing.residue ↥A) hker K

  obtain ⟨eK, ε, heK1, hε, hqϖ, G', H', w, hw', hGH, hmax, hpr1, hpr2, hnm1, hnm2, hsp1, hsp2⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
      (IsLocalRing.residue ↥A) a ha ha2 hp5 hw K x hx ϖ hϖ

  obtain ⟨hG, hG'⟩ :=
    ModularCurve.gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
      (IsLocalRing.residue ↥A) hker hp5 a ha ha2 hw K ϖ hϖ eK ε hε hqϖ G' H' w hw' hGH hmax heK1 hpr1 hpr2 hnm1
      hnm2 hsp1 hsp2

  have hex : ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * p))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ))))) ∧
      ((An.param : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))
        = (G' : LaurentSeries (AlgebraicClosure ℚ)) ∧
      An.modulus = ((p : ℕ) : ↥A) ^ jWidth a := by
    rcases hw with rfl | rfl
    · obtain ⟨An, An', h1, hdom, hpar, hmod⟩ :=
        ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes (IsLocalRing.residue ↥A)
          hker hp5 ha K ϖ hϖ eK ε hε hqϖ G' H' w hw' hGH hmax heK1 hpr1 hpr2 hnm1 hnm2 hsp1 hsp2
      exact ⟨An, An', h1, hdom, hpar, by rw [hmod, jWidth_of_eq_zero rfl]⟩
    · obtain ⟨An, An', h1, hdom, hpar, hmod⟩ :=
        ModularCurve.exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes
          (IsLocalRing.residue ↥A) hker hp5 ha K ϖ hϖ eK ε hε hqϖ G' H' w hw' hGH hmax heK1 hpr1 hpr2 hnm1
          hnm2 hsp1 hsp2
      exact ⟨An, An', h1, hdom, hpar, by
        rw [hmod, jWidth_of_eq_1728 rfl (ModularCurve.WPkgProof.ofNat1728_ne_zero (IsLocalRing.ResidueField ↥A) hp5)]⟩
  obtain ⟨An, An', h1, hdom, hpar, hmod⟩ := hex
  obtain ⟨hdomEq, hmodEq, hmod0, hprod⟩ := h1

  have hmodQ : An'.param * An.param
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (((p : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) := by
    rw [hprod, hmod]; push_cast; rfl
  have hmod' : An'.param * An.param
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((An'.modulus : ↥A) : AlgebraicClosure ℚ) := by
    rw [hprod, hmodEq]
  have hmodw : An'.modulus = ((p : ℕ) : ↥A) ^ jWidth a := by rw [hmodEq, hmod]
  have hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An'.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))) := by
    intro W; rw [hdomEq]; exact hdom W

  have hatt0 :=
    ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne p A
      hp5 C0 x0 a ha ha2 hw hnodes0 An An.param rfl hdom (hG An.param hpar) An'.param hmodQ
      (hG' An.param An'.param hpar hmodQ) hunit0 hordres0
  have hatti :=
    ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne p A
      hp5 Ci xi a ha ha2 hw hnodesi An' An'.param An.param rfl hmod' hmodw hdom' (hG' An.param An'.param hpar hmodQ)
      (hG An.param hpar) huniti hordresi
  exact ⟨An, An', ⟨hdomEq, hmodEq, hmod0, hprod⟩, hatt0, hatti, hdom, hmod⟩

end S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
end P2MW
export P2MW.S_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne (solution)
