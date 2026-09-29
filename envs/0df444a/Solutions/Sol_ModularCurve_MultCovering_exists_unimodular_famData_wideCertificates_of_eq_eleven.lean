-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/12877607-9eb5-51ea-a833-b18cae2f3e8a

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_eq_zero_of_t_eq_one
import Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_MultCovering_neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

namespace W811

scoped instance instFactPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

def h₀ : Fin 3 → ℕ := ![0, 2, 3]

theorem h₀_injective : ∀ a b : Fin 3, h₀ a = h₀ b → a = b := by decide

def kexp (a b : Fin 3) : ℕ := (max 0 ((h₀ a : ℤ) - (h₀ b : ℤ))).toNat

theorem kexp_cast (a b : Fin 3) : ((kexp a b : ℕ) : ℤ) = max 0 ((h₀ a : ℤ) - (h₀ b : ℤ)) :=
  Int.toNat_of_nonneg (le_max_left _ _)

theorem kexp_val : ∀ a b : Fin 3, kexp a b = !![0, 0, 0; 2, 0, 0; 3, 1, 0] a b := by decide

def dn (n₁ n₂ n₃ : ℕ) : Matrix (Fin 3) (Fin 3) ℕ := !![1, 0, 0; n₁, 1, n₃; 0, n₂, 1]

theorem dn_le_one {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ 1) (h2 : n₂ ≤ 1) (h3 : n₃ ≤ 1) :
    ∀ a b, dn n₁ n₂ n₃ a b ≤ 1 := by
  intro a b; fin_cases a <;> fin_cases b <;> simp [dn] <;> assumption

def d₀ (n₁ n₂ n₃ : ℕ) (a b : Fin 3) : ZMod 11 := (dn n₁ n₂ n₃ a b : ZMod 11)

theorem d₀_val {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ 1) (h2 : n₂ ≤ 1) (h3 : n₃ ≤ 1) (a b : Fin 3) :
    (d₀ n₁ n₂ n₃ a b).val = dn n₁ n₂ n₃ a b := by
  unfold d₀; rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by have := dn_le_one h1 h2 h3 a b; omega)

def U₀ (n₁ n₂ n₃ : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun a b => (11:ℚ) ^ kexp a b * (dn n₁ n₂ n₃ a b : ℚ)

def Dq (n₂ n₃ : ℕ) : ℚ := 1 - 11 * (n₃ : ℚ) * n₂

def wz (n₁ n₂ n₃ : ℕ) : Matrix (Fin 3) (Fin 3) ℤ := !![1 - 11 * (n₃:ℤ) * n₂, 0, 0; -(n₁:ℤ), 1, -(n₃:ℤ); (n₁:ℤ) * n₂, -(n₂:ℤ), 1]

def W₀ (n₁ n₂ n₃ : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := fun a b => (11:ℚ) ^ kexp a b * (wz n₁ n₂ n₃ a b : ℚ)

def V₀ (n₁ n₂ n₃ : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := (Dq n₂ n₃)⁻¹ • W₀ n₁ n₂ n₃

theorem V₀_apply (n₁ n₂ n₃ : ℕ) (a b : Fin 3) :
    V₀ n₁ n₂ n₃ a b = (11:ℚ) ^ kexp a b * (wz n₁ n₂ n₃ a b : ℚ) / Dq n₂ n₃ := by
  simp only [V₀, W₀, Matrix.smul_apply, smul_eq_mul]; ring

theorem Dq_ne_zero (n₂ n₃ : ℕ) : Dq n₂ n₃ ≠ 0 := by
  unfold Dq
  intro h
  have h1 : ((11 * (n₃ * n₂) : ℕ) : ℚ) = ((1:ℕ):ℚ) := by push_cast; linarith
  have h2 := Nat.cast_injective h1
  exact absurd (Dvd.intro _ h2) (by decide)

theorem padicValRat_Dq (n₂ n₃ : ℕ) : padicValRat 11 (Dq n₂ n₃) = 0 := by
  have : Dq n₂ n₃ = ((1 - 11 * ((n₃:ℤ) * n₂) : ℤ) : ℚ) := by unfold Dq; push_cast; ring
  rw [this, padicValRat.of_int]
  suffices h : padicValInt 11 (1 - 11 * ((n₃:ℤ) * n₂)) = 0 by simp [h]
  apply padicValInt.eq_zero_of_not_dvd
  generalize (n₃:ℤ) * n₂ = k
  push_cast
  omega

theorem U₀_mul_W₀ (n₁ n₂ n₃ : ℕ) : U₀ n₁ n₂ n₃ * W₀ n₁ n₂ n₃ = Dq n₂ n₃ • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U₀, W₀, kexp_val, dn, wz, Dq, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

theorem U₀_mul_V₀ (n₁ n₂ n₃ : ℕ) : U₀ n₁ n₂ n₃ * V₀ n₁ n₂ n₃ = 1 := by
  rw [V₀, Matrix.mul_smul, U₀_mul_W₀, smul_smul, inv_mul_cancel₀ (Dq_ne_zero _ _), one_smul]

theorem v11_pow (k : ℕ) : padicValRat 11 ((11:ℚ)^k) = k := by
  rw [show (11:ℚ) = ((11:ℕ):ℚ) by norm_num, padicValRat.pow, padicValRat.self (by norm_num)]
  ring

theorem natCast_val_nonneg (n : ℕ) : 0 ≤ padicValRat 11 (n:ℚ) := by
  rw [padicValRat.of_nat]; exact_mod_cast Nat.zero_le _

theorem intCast_val_nonneg (z : ℤ) : 0 ≤ padicValRat 11 (z:ℚ) := by
  rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _

theorem key_val (k : ℕ) (m D : ℚ) (hm : m ≠ 0) (hm0 : 0 ≤ padicValRat 11 m) (hD : D ≠ 0)
    (hD0 : padicValRat 11 D = 0) :
    (k : ℤ) ≤ padicValRat 11 ((11:ℚ)^k * m / D) := by
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ (by norm_num)) hm) hD,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hm, v11_pow, hD0]
  linarith

theorem key_val' (k : ℕ) (m : ℚ) (hm : m ≠ 0) (hm0 : 0 ≤ padicValRat 11 m) :
    (k : ℤ) ≤ padicValRat 11 ((11:ℚ)^k * m) := by
  simpa using key_val k m 1 hm hm0 one_ne_zero (by simp)

theorem hU₀ (n₁ n₂ n₃ : ℕ) (a b : Fin 3) :
    max 0 ((h₀ a : ℤ) - (h₀ b : ℤ)) ≤ padicValRat 11 (U₀ n₁ n₂ n₃ a b) ∨ U₀ n₁ n₂ n₃ a b = 0 := by
  by_cases h : dn n₁ n₂ n₃ a b = 0
  · right; simp [U₀, h]
  · left; rw [← kexp_cast]
    exact key_val' (kexp a b) _ (by exact_mod_cast h) (natCast_val_nonneg _)

theorem hV₀ (n₁ n₂ n₃ : ℕ) (a b : Fin 3) :
    max 0 ((h₀ a : ℤ) - (h₀ b : ℤ)) ≤ padicValRat 11 (V₀ n₁ n₂ n₃ a b) ∨ V₀ n₁ n₂ n₃ a b = 0 := by
  rw [V₀_apply]
  by_cases h : wz n₁ n₂ n₃ a b = 0
  · right; simp [h]
  · left; rw [← kexp_cast]
    exact key_val (kexp a b) _ _ (by exact_mod_cast h) (intCast_val_nonneg _) (Dq_ne_zero _ _) (padicValRat_Dq _ _)

theorem U₀_zero (n₁ n₂ n₃ : ℕ) (b : Fin 3) : U₀ n₁ n₂ n₃ 0 b = if b = 0 then 1 else 0 := by
  fin_cases b <;> simp [U₀, kexp_val, dn]

theorem ord_add_eq_left {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)
    {f g : F} (hf : f ≠ 0) (h : g = 0 ∨ v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  by_cases hg : g = 0
  · rw [hg, add_zero]
  · rcases h with h | h
    · exact absurd h hg
    · exact AlgebraicCurve.Place.ord_add_eq_of_lt v hf hg h

theorem ord_add_eq_right {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)
    {f g : F} (hf : f ≠ 0) (h : g = 0 ∨ v.ord f < v.ord g) : v.ord (g + f) = v.ord f := by
  rw [add_comm]; exact ord_add_eq_left v hf h

end W811
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven.W811"

namespace W811

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering ModularCurve

theorem card_members_eq (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r) :
    Fintype.card {l : Fin r // 1 ≤ (l : ℕ)} = mAnnuli p := by
  obtain ⟨hintT, -, P, -, hPli, hspan⟩ := Φ.t_inf A hA Γ
  have h1 : Module.finrank (ResidueField ↥A)
      (Submodule.span (ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l))
        = Fintype.card {l : Fin r // 1 ≤ (l : ℕ)} := finrank_span_eq_card hPli
  rw [hspan] at h1
  rw [← h1]
  exact (Polynomial.degreeLTEquiv (ResidueField ↥A) (mAnnuli p)).finrank_eq.trans (Module.finrank_fin_fun _)

theorem r_eq_three (p : ℕ) [Fact p.Prime] (hm : mAnnuli p = 2) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) : r = 3 := by
  have hc := card_members_eq p A hA Γ Φ
  rw [hm, Fintype.card_subtype] at hc
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hc
    · exact h
  have : (Finset.univ.filter fun l : Fin r => 1 ≤ (l : ℕ)) = Finset.univ.erase ⟨0, hr⟩ := by
    ext l; simp [Nat.one_le_iff_ne_zero, Fin.ext_iff]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
  omega

end W811
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven.W811"

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering ModularCurve

set_option maxHeartbeats 8000000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp11 : p = 11) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers),
      IsUnit U ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
        ∨ U i j = 0) ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
        ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r),
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)
          = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ)) ∧
      (∀ l : Fin r, 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 ∨ hasseExp Φ.toFamData l = 3) ∧
      (∃ l₂ l₃ : Fin r, l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
        hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 3) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 →
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 1) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 3 →
        (ssValue Γ e = 0 → (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 1) ∧
        (ssValue Γ e = 1728 → (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 2)) := by
  classical
  subst hp11
  obtain rfl : r = 3 := W811.r_eq_three 11 (by decide) A hA Γ Φ

  obtain ⟨μ, -, -, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out) A hA
  obtain ⟨hintI, l₂, l₃, hne, hl₂, hl₃, hh₂, hh₃, hP⟩ :=
    ModularCurve.MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven 11 rfl A hA Γ Δ Φ hint hLI μ hμA
  obtain ⟨hintB, hbd⟩ :=
    ModularCurve.MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero 11 A hA Γ Δ Φ
  obtain ⟨hintN, hnd⟩ := ModularCurve.MultCovering.infChart_nodeData 11 A hA Γ Φ
  have hSSV : ∀ e : Fin (mAnnuli 11), ssValue Γ e = 0 ∨ ssValue Γ e = 1728 := by
    exact ModularCurve.MultCovering.ssValue_eq_zero_or_eq_1728_of_eq_eleven 11 rfl A hA Γ

  have h20 : l₂ ≠ 0 := by rintro rfl; simp at hl₂
  have h30 : l₃ ≠ 0 := by rintro rfl; simp at hl₃
  have htri : ∀ i : Fin 3, i = 0 ∨ i = l₂ ∨ i = l₃ := by
    intro i
    have h1 : (l₂ : ℕ) ≠ (l₃ : ℕ) := fun h => hne (Fin.ext h)
    have hi := i.isLt; have h2 := l₂.isLt; have h3 := l₃.isLt
    have : (i : ℕ) = 0 ∨ (i : ℕ) = (l₂ : ℕ) ∨ (i : ℕ) = (l₃ : ℕ) := by omega
    rcases this with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have ht0 : Φ.t 0 = 1 := Φ.t_zero 0 rfl
  have hh0 : hasseExp Φ.toFamData 0 = 0 := ModularCurve.MultCovering.hasseExp_eq_zero_of_t_eq_one _ 0 ht0

  let κ : Fin 3 → Fin 3 := fun i => if i = l₂ then 1 else if i = l₃ then 2 else 0
  have hκ0 : κ 0 = 0 := by simp [κ, h20.symm, h30.symm]
  have hκ2 : κ l₂ = 1 := by simp [κ]
  have hκ3 : κ l₃ = 2 := by simp [κ, hne.symm]
  have hleft : Function.LeftInverse ![0, l₂, l₃] κ := by
    intro i; rcases htri i with h | h | h <;> rw [h]
    · rw [hκ0]; rfl
    · rw [hκ2]; rfl
    · rw [hκ3]; rfl
  have hright : Function.RightInverse ![0, l₂, l₃] κ := by
    intro b; fin_cases b
    · exact hκ0
    · exact hκ2
    · exact hκ3
  let σ : Fin 3 ≃ Fin 3 := ⟨κ, ![0, l₂, l₃], hleft, hright⟩
  have hσ0 : σ 0 = 0 := hκ0
  have hσ2 : σ l₂ = 1 := hκ2
  have hσ3 : σ l₃ = 2 := hκ3
  have hσs0 : σ.symm 0 = 0 := rfl
  have hσs1 : σ.symm 1 = l₂ := rfl
  have hσs2 : σ.symm 2 = l₃ := rfl
  have hh : ∀ i, hasseExp Φ.toFamData i = W811.h₀ (σ i) := by
    intro i; rcases htri i with h | h | h <;> rw [h]
    · rw [hh0, hσ0]; rfl
    · rw [hh₂, hσ2]; rfl
    · rw [hh₃, hσ3]; rfl
  have sum3 : ∀ (f : Fin 3 → ↥(modularFunctionFieldC (ResidueField ↥A) 1)), ∑ j, f j = f 0 + f l₂ + f l₃ := by
    intro f; rw [← Equiv.sum_comp σ.symm f, Fin.sum_univ_three, hσs0, hσs1, hσs2]

  obtain ⟨gb, hgb⟩ : ∃ gb : Fin 3 → ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      gb = fun j => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ := ⟨_, rfl⟩
  obtain ⟨tb, htb⟩ : ∃ tb : Fin 3 → ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      tb = fun j => (infChart Γ).residue ⟨Φ.t j, hintI j⟩ := ⟨_, rfl⟩
  have hgbne : ∀ j, gb j ≠ 0 := fun j => by rw [hgb]; exact hLI.ne_zero j
  have hgb0raw : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩ = 1 := by
    have hg : goodFamilyZero Φ.toFamData 0 = 1 := by
      unfold goodFamilyZero; rw [hh0, pow_zero, map_one, inv_one, one_mul (Φ.t 0)]; exact ht0
    have e1 : (⟨goodFamilyZero Φ.toFamData 0, hint 0⟩ : (zeroChart Γ).integers) = 1 := Subtype.ext hg
    rw [e1, map_one]
  have hgb0 : gb 0 = 1 := by rw [hgb]; exact hgb0raw

  have h1728 : (1728 : ResidueField ↥A) ≠ 0 := by
    intro h
    have : ((1728 : ℕ) : ResidueField ↥A) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField ↥A) 11] at this
    omega
  have hm2 : mAnnuli 11 = 2 := by decide
  have he : (∃ e : Fin (mAnnuli 11), ssValue Γ e = 0) ∧ (∃ e : Fin (mAnnuli 11), ssValue Γ e = 1728) := by
    let e0 : Fin (mAnnuli 11) := ⟨0, by rw [hm2]; norm_num⟩
    let e1 : Fin (mAnnuli 11) := ⟨1, by rw [hm2]; norm_num⟩
    have hne01 : e0 ≠ e1 := by intro h; have := congrArg Fin.val h; simp [e0, e1] at this
    have hss := fun h => hne01 (ssValue_injective Γ h)
    rcases hSSV e0 with h0 | h0 <;> rcases hSSV e1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hss
    · exact ⟨⟨e0, h0⟩, ⟨e1, h1⟩⟩
    · exact ⟨⟨e1, h1⟩, ⟨e0, h0⟩⟩
    · exact absurd (h0.trans h1.symm) hss
  obtain ⟨⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := he
  have htbne2 : tb l₂ ≠ 0 := by
    intro h
    have h1 : (nodeTgt Γ e₁).ord (tb l₂) = 1 := by rw [htb]; exact ((hP e₁).1 he₁).1
    rw [h, Place.ord_zero] at h1
    exact zero_ne_one h1
  have htbne3 : tb l₃ ≠ 0 := by
    intro h
    have h1 : (nodeTgt Γ e₀).ord (tb l₃) = 1 := by rw [htb]; exact ((hP e₀).2 he₀).1
    rw [h, Place.ord_zero] at h1
    exact zero_ne_one h1

  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = if ∃ e, ssValue Γ e = 0 ∧ 1 ≤ (nodeSrc Γ e).ord (gb l₂) then 1 else 0 :=
    ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, n₂ = if ∃ e, ssValue Γ e = 1728 ∧ 0 ≤ (nodeSrc Γ e).ord (gb l₃) then 1 else 0 :=
    ⟨_, rfl⟩
  obtain ⟨n₃, hn₃⟩ : ∃ n₃ : ℕ, n₃ = if ∃ e, ssValue Γ e = 0 ∧ 2 ≤ (nodeTgt Γ e).ord (tb l₂) then 1 else 0 :=
    ⟨_, rfl⟩
  have hn₁1 : n₁ ≤ 1 := by rw [hn₁]; split_ifs <;> norm_num
  have hn₂1 : n₂ ≤ 1 := by rw [hn₂]; split_ifs <;> norm_num
  have hn₃1 : n₃ ≤ 1 := by rw [hn₃]; split_ifs <;> norm_num

  obtain ⟨d, hd⟩ : ∃ d : Fin 3 → Fin 3 → ZMod 11, d = fun i j => W811.d₀ n₁ n₂ n₃ (σ i) (σ j) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin 3) (Fin 3) ℚ, U = fun i j =>
      ((11 : ℕ) : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))).toNat
        * ((d i j).val : ℚ) := ⟨_, rfl⟩
  have hdv : ∀ i j, (d i j).val = W811.dn n₁ n₂ n₃ (σ i) (σ j) := by
    intro i j; rw [hd]; exact W811.d₀_val hn₁1 hn₂1 hn₃1 _ _
  have hUσ : ∀ i j, U i j = W811.U₀ n₁ n₂ n₃ (σ i) (σ j) := by
    intro i j; rw [hU]; dsimp only; rw [hh i, hh j, hdv, Nat.cast_ofNat]; rfl
  have hUeq : U = (W811.U₀ n₁ n₂ n₃).submatrix σ σ := by ext i j; exact hUσ i j
  have hUV : U * (W811.V₀ n₁ n₂ n₃).submatrix σ σ = 1 := by
    rw [hUeq, Matrix.submatrix_mul_equiv, W811.U₀_mul_V₀, Matrix.submatrix_one_equiv]
  have hUunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_right_inverse hUV)
  have hUinv : U⁻¹ = (W811.V₀ n₁ n₂ n₃).submatrix σ σ := Matrix.inv_eq_right_inv hUV
  have hUfil : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat 11 (U i j)
      ∨ U i j = 0 := by
    intro i j; rw [hUσ, hh i, hh j]; exact W811.hU₀ n₁ n₂ n₃ (σ i) (σ j)
  have hUinvfil : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))
      ≤ padicValRat 11 (U⁻¹ i j) ∨ U⁻¹ i j = 0 := by
    intro i j; rw [hUinv, Matrix.submatrix_apply, hh i, hh j]; exact W811.hV₀ n₁ n₂ n₃ (σ i) (σ j)
  have hU0 : ∀ i j : Fin 3, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0 := by
    intro i j hi
    obtain rfl : i = 0 := Fin.ext hi
    rw [hUσ, hσ0, W811.U₀_zero]
    rcases htri j with h | h | h <;> rw [h]
    · simp [hσ0]
    · rw [hσ2, if_neg (by decide), if_neg (by simpa using h20)]
    · rw [hσ3, if_neg (by decide), if_neg (by simpa using h30)]
  have hUd : ∀ i j, U i j = ((11 : ℕ) : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ)
      - (hasseExp Φ.toFamData j : ℤ))).toNat * ((d i j).val : ℚ) := fun i j => by rw [hU]
  have hblock : ∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin 3 // hasseExp Φ.toFamData a = c}) =>
      d i.1 j.1)) := by
    intro c
    have : (Matrix.of fun (i j : {a : Fin 3 // hasseExp Φ.toFamData a = c}) => d i.1 j.1) = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      by_cases hij : i = j
      · subst hij
        rw [Matrix.of_apply, Matrix.one_apply_eq, hd]
        show ((W811.dn n₁ n₂ n₃ (σ i) (σ i) : ℕ) : ZMod 11) = 1
        have : W811.dn n₁ n₂ n₃ (σ i) (σ i) = 1 := by
          generalize σ i = a; fin_cases a <;> simp [W811.dn]
        rw [this, Nat.cast_one]
      · exfalso; apply hij
        have h' := hi.trans hj.symm
        rw [hh i, hh j] at h'
        exact σ.injective (W811.h₀_injective _ _ h')
    rw [this, Matrix.det_one]; exact isUnit_one

  obtain ⟨D', hint', hintI', htRat, ht, hexp, hgfz, hLI', hRI, hRZ⟩ :=
    ModularCurve.MultCovering.exists_famData_of_bifiltered_digits 11 (by norm_num) A hA Γ Δ Φ (fun l => hintI l) hint
      hLI U d hUunit hUfil hUinvfil hU0 hUd hblock

  have hdk : ∀ i j, ((d i j).val : ResidueField ↥A) = ((W811.dn n₁ n₂ n₃ (σ i) (σ j) : ℕ) : ResidueField ↥A) :=
    fun i j => by rw [hdv]
  have hZ0 : (zeroChart Γ).residue ⟨goodFamilyZero D' 0, hint' 0⟩ = 1 := by
    rw [hRZ, sum3]; simp [hdk, hσ0, hσ2, hσ3, hh0, hh₂, hh₃, W811.dn, hgb0raw, hgb]
  have hZ2 : (zeroChart Γ).residue ⟨goodFamilyZero D' l₂, hint' l₂⟩
      = algebraMap (ResidueField ↥A) _ (n₁ : ResidueField ↥A) + gb l₂ := by
    rw [hRZ, sum3]; simp [hdk, hσ0, hσ2, hσ3, hh0, hh₂, hh₃, W811.dn, hgb0raw, hgb]
  have hZ3 : (zeroChart Γ).residue ⟨goodFamilyZero D' l₃, hint' l₃⟩
      = algebraMap (ResidueField ↥A) _ (n₂ : ResidueField ↥A) * gb l₂ + gb l₃ := by
    rw [hRZ, sum3]; simp [hdk, hσ0, hσ2, hσ3, hh0, hh₂, hh₃, W811.dn, hgb0raw, hgb]
  have hI2 : (infChart Γ).residue ⟨D'.t l₂, hintI' l₂⟩
      = tb l₂ + algebraMap (ResidueField ↥A) _ (n₃ : ResidueField ↥A) * tb l₃ := by
    rw [hRI, sum3]; simp [hdk, hσ0, hσ2, hσ3, hh0, hh₂, hh₃, W811.dn, htb]
  have hI3 : (infChart Γ).residue ⟨D'.t l₃, hintI' l₃⟩ = tb l₃ := by
    rw [hRI, sum3]; simp [hdk, hσ0, hσ2, hσ3, hh0, hh₂, hh₃, W811.dn, htb]

  have hw0 : ∀ e, ssValue Γ e = 0 → jWidth (ssValue Γ e) = 3 := fun e h => by rw [h]; simp [jWidth]
  have hw1 : ∀ e, ssValue Γ e = 1728 → jWidth (ssValue Γ e) = 2 := fun e h => by rw [h]; simp [jWidth, h1728]

  have huq : ∀ e e' (a : ResidueField ↥A), ssValue Γ e = a → ssValue Γ e' = a → e' = e :=
    fun e e' a h h' => ssValue_injective Γ (h'.trans h.symm)

  refine ⟨U, D', hint', hintI', hUunit, hUfil, hUinvfil, hU0, htRat, ht, hexp, hgfz, hLI', ?_, ?_,
    ⟨l₂, l₃, hne, hl₂, hl₃, hh₂, hh₃⟩, ?_, ?_⟩
  ·
    intro e l
    rcases hSSV e with hss | hss
    ·
      rw [hw0 e hss]
      rcases htri l with h | h | h <;> rw [h]
      · rw [hZ0, hh0, Place.ord_one]; norm_num
      · rw [hZ2, hh₂]; norm_num
        by_cases hC : ∃ e, ssValue Γ e = 0 ∧ 1 ≤ (nodeSrc Γ e).ord (gb l₂)
        · rw [if_pos hC] at hn₁; subst hn₁
          obtain ⟨e', he', hord⟩ := hC
          obtain rfl := huq e e' 0 hss he'
          try simp only [Nat.cast_one]
          rw [W811.ord_add_eq_left _ one_ne_zero (Or.inr ?_), Place.ord_one]
          rw [Place.ord_one]; omega
        · rw [if_neg hC] at hn₁; subst hn₁
          try simp only [Nat.cast_zero, zero_add]
          have hb : 0 ≤ (nodeSrc Γ e).ord (gb l₂) := by
            have := hbd e l₂; rw [hh₂, hw0 e hss] at this; simpa [hgb] using this
          have : ¬ 1 ≤ (nodeSrc Γ e).ord (gb l₂) := fun h1 => hC ⟨e, hss, h1⟩
          omega
      · rw [hZ3, hh₃]; norm_num
        have h3 : (nodeSrc Γ e).ord (gb l₃) = -1 := by simpa [hgb] using ((hP e).2 hss).2
        have hb : 0 ≤ (nodeSrc Γ e).ord (gb l₂) := by
          have := hbd e l₂; rw [hh₂, hw0 e hss] at this; simpa [hgb] using this
        rw [W811.ord_add_eq_right _ (hgbne l₃) ?_, h3]
        rcases (by omega : n₂ = 0 ∨ n₂ = 1) with hz | hz <;> subst hz
        · left; simp
        · right; simp only [Nat.cast_one, one_mul]; omega
    ·
      rw [hw1 e hss]
      rcases htri l with h | h | h <;> rw [h]
      · rw [hZ0, hh0, Place.ord_one]; norm_num
      · rw [hZ2, hh₂]; norm_num
        have h2 : (nodeSrc Γ e).ord (gb l₂) = -1 := by simpa [hgb] using ((hP e).1 hss).2.1
        rcases (by omega : n₁ = 0 ∨ n₁ = 1) with hz | hz <;> subst hz
        · simpa using h2
        · simp only [Nat.cast_one]
          rw [W811.ord_add_eq_right _ (hgbne l₂) (Or.inr ?_), h2]
          rw [Place.ord_one]; omega
      · rw [hZ3, hh₃]; norm_num
        have h2 : (nodeSrc Γ e).ord (gb l₂) = -1 := by simpa [hgb] using ((hP e).1 hss).2.1
        by_cases hC : ∃ e, ssValue Γ e = 1728 ∧ 0 ≤ (nodeSrc Γ e).ord (gb l₃)
        · rw [if_pos hC] at hn₂; subst hn₂
          obtain ⟨e', he', hord⟩ := hC
          obtain rfl := huq e e' 1728 hss he'
          simp only [Nat.cast_one, one_mul]
          rw [W811.ord_add_eq_left _ (hgbne l₂) (Or.inr ?_), h2]
          omega
        · rw [if_neg hC] at hn₂; subst hn₂
          simp only [Nat.cast_zero, zero_mul, zero_add]
          have hb : -1 ≤ (nodeSrc Γ e).ord (gb l₃) := by
            have := hbd e l₃; rw [hh₃, hw1 e hss] at this; simpa [hgb] using this
          have : ¬ 0 ≤ (nodeSrc Γ e).ord (gb l₃) := fun h1 => hC ⟨e, hss, h1⟩
          omega
  ·
    intro l hl
    rcases htri l with h | h | h <;> rw [h]
    · rw [h] at hl; simp at hl
    · exact Or.inl hh₂
    · exact Or.inr hh₃
  ·
    intro e l hl hl2
    obtain rfl : l = l₂ := by
      rcases htri l with h | h | h
      · rw [h, hh0] at hl2; exact absurd hl2 (by norm_num)
      · exact h
      · rw [h, hh₃] at hl2; exact absurd hl2 (by norm_num)
    rw [hI2]
    rcases hSSV e with hss | hss
    · have ht3 : (nodeTgt Γ e).ord (tb l₃) = 1 := by simpa [htb] using ((hP e).2 hss).1
      have hb : 1 ≤ (nodeTgt Γ e).ord (tb l) := by simpa [htb] using (hnd e).1 l hl
      by_cases hC : ∃ e, ssValue Γ e = 0 ∧ 2 ≤ (nodeTgt Γ e).ord (tb l)
      · rw [if_pos hC] at hn₃; subst hn₃
        obtain ⟨e', he', hord⟩ := hC
        obtain rfl := huq e e' 0 hss he'
        rw [Nat.cast_one, map_one, one_mul, W811.ord_add_eq_right _ htbne3 (Or.inr ?_), ht3]
        omega
      · rw [if_neg hC] at hn₃; subst hn₃
        rw [Nat.cast_zero, map_zero, zero_mul, add_zero]
        have : ¬ 2 ≤ (nodeTgt Γ e).ord (tb l) := fun h1 => hC ⟨e, hss, h1⟩
        omega
    · have ht2 : (nodeTgt Γ e).ord (tb l) = 1 := by simpa [htb] using ((hP e).1 hss).1
      have ht3 : (nodeTgt Γ e).ord (tb l₃) = 2 := by simpa [htb] using ((hP e).1 hss).2.2
      rw [W811.ord_add_eq_left _ htbne2 ?_, ht2]
      rcases Nat.eq_zero_or_pos n₃ with hz | hz
      · left; rw [hz, Nat.cast_zero, map_zero, zero_mul]
      · right
        obtain rfl : n₃ = 1 := by omega
        rw [Nat.cast_one, map_one, one_mul]; omega
  ·
    intro e l hl hl3
    obtain rfl : l = l₃ := by
      rcases htri l with h | h | h
      · rw [h, hh0] at hl3; exact absurd hl3 (by norm_num)
      · rw [h, hh₂] at hl3; exact absurd hl3 (by norm_num)
      · exact h
    rw [hI3]
    exact ⟨fun hss => by simpa [htb] using ((hP e).2 hss).1, fun hss => by simpa [htb] using ((hP e).1 hss).2.2⟩

end S_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven (solution)
