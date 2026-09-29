-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/091da690-a701-56a9-97be-6945f7144232

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.redRes CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_mem_laurentBaseChange qExpand jq jq_mem jqd_mem_full modularFunctionField_le_full jWidth frickeInvolutionBar modularFunctionFieldBar ssJSet NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_ofNat1728 NodeLocalized.exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed deg_eq_one_modularFunctionFieldBar"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict modularEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint exists_gaussCoordinate_of_crossingPresentation_ofNat1728 exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed"
namespace TubeUnit
p2m_open "ModularCurve.NodeLocalized ModularCurve"

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation.ModularCurve.NodeLocalized"

section Helpers

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] (red : A →+* k)

private theorem isRational_of_deg_eq_one {L F : Type*} [Field L] [Field F]
    [Algebra L F] (v : Place L F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

private theorem isRational_place_modularFunctionFieldBar' (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : v.IsRational :=
  isRational_of_deg_eq_one v (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)

omit [CharP k q] in

private theorem ne_zero_of_modularRedLocHom_ne_zero {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
  intro h0
  apply hgu
  have h : (⟨_, hg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 :=
    Subtype.ext h0
  rw [h, map_zero]

omit [CharP k q] in

private theorem exists_inv_mem_modularLocalized {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0) :
    ∃ h : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩
        = (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩)⁻¹ := by
  have hgL : (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    ne_zero_of_modularRedLocHom_ne_zero red hg hgu
  have hinvL : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by
    norm_cast
  obtain ⟨r, s, hs, heq⟩ := id hg
  have hsne := CharPReduction.redRes_ne_zero_of_notMem (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hs
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
    (⟨_, hg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) heq
  have hrne : CharPReduction.redRes A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hgu hsne
  have hrk : r ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hrne
  have hmem : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    refine ⟨s, r, hrk, ?_⟩
    rw [hinvL]
    calc ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ * r
        = ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹
          * ((g : LaurentSeries (AlgebraicClosure ℚ)) * s) := by rw [heq]
      _ = s := inv_mul_cancel_left₀ hgL _
  refine ⟨hmem, ?_⟩
  have hone : (⟨_, hmem⟩ * ⟨_, hg⟩ :
      ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 := by
    apply Subtype.ext
    show ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      * (g : LaurentSeries (AlgebraicClosure ℚ)) = 1
    rw [hinvL, inv_mul_cancel₀ hgL]
  have hmul := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hone
  rw [map_mul, map_one] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

omit [CharP k q] in

private theorem exists_pow_mem_modularLocalized (n : ℕ) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    ∃ h : ((g ^ n : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩
        = (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩) ^ n := by
  induction n with
  | zero =>
    have h1 : ((g ^ 0 : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
      push_cast
      rfl
    have hmem : ((g ^ 0 : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := h1 ▸ one_mem _
    refine ⟨hmem, ?_⟩
    have hel : (⟨_, hmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 :=
      Subtype.ext h1
    calc CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hmem⟩
        = CharPReduction.modularRedLocHom (1 * q) A.toSubring red 1 := congrArg _ hel
      _ = 1 := map_one _
      _ = _ := (pow_zero _).symm
  | succ n ih =>
    obtain ⟨hn, hres⟩ := ih
    have hcoe : ((g ^ (n + 1) : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ))
        = ((g ^ n : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          * (g : LaurentSeries (AlgebraicClosure ℚ)) := by
      push_cast
      ring
    have hmem : ((g ^ (n + 1) : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [hcoe]
      exact mul_mem hn hg
    refine ⟨hmem, ?_⟩
    have hel : (⟨_, hmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
        = ⟨_, hn⟩ * ⟨_, hg⟩ := Subtype.ext hcoe
    calc CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hmem⟩
        = CharPReduction.modularRedLocHom (1 * q) A.toSubring red (⟨_, hn⟩ * ⟨_, hg⟩) :=
          congrArg _ hel
      _ = _ := by rw [map_mul, hres, pow_succ]

omit [CharP k q] in

private theorem exists_zpow_mem_modularLocalized (m : ℤ) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0) :
    ∃ h : ((g ^ m : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩
        = (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩) ^ m := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · obtain ⟨hn, hres⟩ := exists_pow_mem_modularLocalized red n hg
    have hcoe : ((g ^ (n : ℤ) : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ))
        = ((g ^ n : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [zpow_natCast]
    refine ⟨hcoe ▸ hn, ?_⟩
    have hel : (⟨_, hcoe ▸ hn⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
        = ⟨_, hn⟩ := Subtype.ext hcoe
    calc CharPReduction.modularRedLocHom (1 * q) A.toSubring red _
        = CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hn⟩ := congrArg _ hel
      _ = _ := by rw [hres, zpow_natCast]
  · have hzp : (g ^ (-(n : ℤ)) : ↥(modularFunctionFieldBar (1 * q)))
        = ((g ^ n : ↥(modularFunctionFieldBar (1 * q))))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    obtain ⟨hn, hresn⟩ := exists_pow_mem_modularLocalized red n hg
    have hnu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hn⟩ ≠ 0 := by
      rw [hresn]
      exact pow_ne_zero _ hgu
    obtain ⟨hi, hresi⟩ := exists_inv_mem_modularLocalized red hn hnu
    have hcoe : ((g ^ (-(n : ℤ)) : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ))
        = (((g ^ n : ↥(modularFunctionFieldBar (1 * q)))⁻¹ :
            ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hzp]
    refine ⟨hcoe ▸ hi, ?_⟩
    have hel : (⟨_, hcoe ▸ hi⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
        = ⟨_, hi⟩ := Subtype.ext hcoe
    calc CharPReduction.modularRedLocHom (1 * q) A.toSubring red _
        = CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hi⟩ := congrArg _ hel
      _ = _ := by rw [hresi, hresn, zpow_neg, zpow_natCast]

omit [CharP k q] in

private theorem exists_mem_ne_zero_of_eq_mul_zpow (n : ℤ) {x g y : ↥(modularFunctionFieldBar (1 * q))}
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hxu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hx⟩ ≠ 0)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0)
    (hy : y = x * g ^ n) :
    ∃ h : (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
  obtain ⟨hgm, hgmres⟩ := exists_zpow_mem_modularLocalized red n hg hgu
  have hcoe : (y : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))
      * ((g ^ n : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hy, MulMemClass.coe_mul]
  have hmem : (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hcoe]
    exact mul_mem hx hgm
  refine ⟨hmem, ?_⟩
  have hsplit : (⟨_, hmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hx⟩ * ⟨_, hgm⟩ :=
    Subtype.ext hcoe
  rw [hsplit, map_mul, hgmres]
  exact mul_ne_zero hxu (zpow_ne_zero _ hgu)

end Helpers

section OrdEval

variable {q : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in

private theorem ord_zpow_eq_zero {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {g : ↥(modularFunctionFieldBar (1 * q))} (hg0 : g ≠ 0) (hord : W.ord g = 0) (m : ℤ) :
    W.ord (g ^ m) = 0 := by
  have hpow : ∀ n : ℕ, W.ord (g ^ n) = 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact W.ord_one
    | succ n ih =>
      rw [pow_succ, W.ord_mul (pow_ne_zero n hg0) hg0, ih, hord, add_zero]
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast]; exact hpow n
  · have hne : g ^ n ≠ 0 := pow_ne_zero _ hg0
    have hsum := W.ord_mul (inv_ne_zero hne) hne
    rw [inv_mul_cancel₀ hne, W.ord_one, hpow n, add_zero] at hsum
    rw [zpow_neg, zpow_natCast]
    exact hsum.symm

omit [Fact q.Prime] in

private theorem evalAt_zpow_of_ord_eq_zero
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hWr : W.IsRational) {g : ↥(modularFunctionFieldBar (1 * q))} (hg0 : g ≠ 0)
    (hord : W.ord g = 0) (m : ℤ) :
    W.evalAt (g ^ m) = (W.evalAt g) ^ m := by
  have hmem1 : g ∈ W.toValuationSubring :=
    GaussReduction.mem_of_ord_nonneg_gen W hg0 hord.ge
  have hmemn : ∀ n : ℕ, g ^ n ∈ W.toValuationSubring := by
    intro n
    refine GaussReduction.mem_of_ord_nonneg_gen W (pow_ne_zero n hg0) ?_
    have h := ord_zpow_eq_zero hg0 hord (n : ℤ)
    rw [zpow_natCast] at h
    rw [h]
  have hpow : ∀ n : ℕ, W.evalAt (g ^ n) = (W.evalAt g) ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact W.evalAt_one
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, GaussReduction.evalAt_mul_of_mem W hWr (hmemn n) hmem1]
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast]
    exact hpow n
  · have hne : g ^ n ≠ 0 := pow_ne_zero _ hg0
    have hordn : W.ord (g ^ n) = 0 := by
      have h := ord_zpow_eq_zero hg0 hord ((n : ℕ) : ℤ)
      rw [zpow_natCast] at h
      exact h
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      StandardAnnulus.evalAt_inv_of_ord_eq_zero W hWr hne hordn, hpow n]

omit [Fact q.Prime] in

private theorem smul_eq_algebraMap_mul (C : AlgebraicClosure ℚ) (f : ↥(modularFunctionFieldBar (1 * q))) :
    C • f = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C * f :=
  Algebra.smul_def C f

omit [Fact q.Prime] in

private theorem ord_const_mul_mul_zpow_eq_zero {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {f G : ↥(modularFunctionFieldBar (1 * q))} {C : AlgebraicClosure ℚ} (hC : C ≠ 0) (hf : f ≠ 0) (hG : G ≠ 0)
    (hfz : W.ord f = 0) (hGz : W.ord G = 0) (n : ℤ) :
    W.ord ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C * f) * G ^ n) = 0 := by
  have hCa : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C ≠ 0 := (_root_.map_ne_zero _).mpr hC
  have hsm : W.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C * f) = 0 := by
    rw [W.ord_mul hCa hf, hfz, StandardAnnulus.ord_algebraMap_eq_zero W hC, add_zero]
  rw [W.ord_mul (mul_ne_zero hCa hf) (zpow_ne_zero _ hG), hsm, ord_zpow_eq_zero hG hGz n, add_zero]

omit [Fact q.Prime] in

private theorem evalAt_const_mul_mul_zpow {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hWr : W.IsRational)
    {f G : ↥(modularFunctionFieldBar (1 * q))} {C : AlgebraicClosure ℚ} (hC : C ≠ 0) (hf : f ≠ 0) (hG : G ≠ 0)
    (hfz : W.ord f = 0) (hGz : W.ord G = 0) (n : ℤ) :
    W.evalAt ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C * f) * G ^ n)
      = C * W.evalAt f * (W.evalAt G) ^ n := by
  have hCa : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C ≠ 0 := (_root_.map_ne_zero _).mpr hC
  have hmalg : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C ∈ W.toValuationSubring := by
    refine GaussReduction.mem_of_ord_nonneg_gen W hCa ?_
    rw [StandardAnnulus.ord_algebraMap_eq_zero W hC]
  have hmf : f ∈ W.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen W hf hfz.ge
  have hmCf : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) C * f ∈ W.toValuationSubring :=
    mul_mem hmalg hmf
  have hmG : G ^ n ∈ W.toValuationSubring := by
    refine GaussReduction.mem_of_ord_nonneg_gen W (zpow_ne_zero _ hG) ?_
    rw [ord_zpow_eq_zero hG hGz n]
  rw [GaussReduction.evalAt_mul_of_mem W hWr hmCf hmG, evalAt_zpow_of_ord_eq_zero hWr hG hGz n,
    GaussReduction.evalAt_mul_of_mem W hWr hmalg hmf, GaussReduction.evalAt_algebraMap_const W hWr C]

end OrdEval

section Twist

variable {q : ℕ} [Fact q.Prime]

omit [Fact q.Prime] in

private theorem smul_mul_zpow_neg_eq (c b : AlgebraicClosure ℚ) (e : ℕ) (n : ℤ)
    (f G : ↥(modularFunctionFieldBar (1 * q))) :
    ((c * b ^ ((e : ℤ) * n)) • f) * G ^ (-n) = (c • f) * ((b ^ e)⁻¹ • G) ^ (-n) := by
  have h : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (b ^ e)⁻¹) ^ (-n)
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (b ^ ((e : ℤ) * n)) := by
    rw [map_inv₀, inv_zpow', neg_neg, ← map_zpow₀, zpow_mul, zpow_natCast]
  rw [smul_eq_algebraMap_mul, smul_eq_algebraMap_mul, smul_eq_algebraMap_mul, mul_zpow, h, map_mul]
  ring

end Twist

end ModularCurve.NodeLocalized.TubeUnit

end

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation.ModularCurve.NodeLocalized"
open ModularCurve.NodeLocalized.TubeUnit in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (ha : (1728 : k) ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (jWidth (1728 : k) * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))}) :
∀ Gf : ↥(modularFunctionFieldBar (1 * q)),
      (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
          (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
            ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) →
          ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
            ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
              ((∃ x : A, red x = (1728 : k) ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (1728 : k) ^ q ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
                ∃ h : W.evalAt f * c⁻¹ * (W.evalAt Gf) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  intro Gf hGfc f hf hford
  have _ := @hmax

  have hpack := ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_ofNat1728 red hker ha hq K
    ϖ hϖ eK ε hε hqϖ heK1 G' H' w hw hGH hpr1 hpr2 hnm1 hnm2 hsp1 hsp2
  obtain ⟨Gf₀, hGf₀c, hG₁, hG₂, hG₁u, hG₂u, hGord⟩ := hpack
  have hGfeq : Gf = Gf₀ := Subtype.ext (hGfc.trans hGf₀c.symm)

  have hnorm := ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd red hker ha hq f
    hf hford
  obtain ⟨c₀, hc₀, m₀, hdvd, h₁, h₂, h₁u, h₂u⟩ := hnorm
  obtain ⟨n, hn⟩ := hdvd
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hC0 : c₀ * ((q : ℕ) : AlgebraicClosure ℚ) ^ m₀ ≠ 0 := mul_ne_zero hc₀ (zpow_ne_zero _ hq0)
  have hg0 : ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (1728 : k))⁻¹ • Gf₀ : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 :=
    fun h0 =>
    ne_zero_of_modularRedLocHom_ne_zero red hG₁ hG₁u (by rw [h0]; rfl)
  have hGf0 : Gf₀ ≠ 0 := fun h => hg0 (by rw [h, smul_eq_algebraMap_mul, mul_zero])

  obtain ⟨f', hf'⟩ : ∃ f' : ↥(modularFunctionFieldBar (1 * q)),
      f' = ((c₀ * ((q : ℕ) : AlgebraicClosure ℚ) ^ m₀) • f) * Gf₀ ^ (-n) := ⟨_, rfl⟩

  have hf'inf : f' = (c₀ • f) * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (1728 : k))⁻¹ • Gf₀) ^ (-n) := by
    rw [hf', hn]
    exact smul_mul_zpow_neg_eq c₀ _ _ n f Gf₀
  obtain ⟨hmem₁', hres₁'⟩ := exists_mem_ne_zero_of_eq_mul_zpow red (-n) h₁ h₁u hG₁ hG₁u hf'inf

  have hf'fr : frickeInvolutionBar (1 * q) f'
      = frickeInvolutionBar (1 * q) ((c₀ * ((q : ℕ) : AlgebraicClosure ℚ) ^ m₀) • f)
        * (frickeInvolutionBar (1 * q) Gf₀) ^ (-n) := by
    rw [hf', map_mul, map_zpow₀]
  obtain ⟨hmem₂', hres₂'⟩ := exists_mem_ne_zero_of_eq_mul_zpow red (-n) h₂ h₂u hG₂ hG₂u hf'fr

  have hford' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = (1728 : k) ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (1728 : k) ^ q ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))
        → W.ord f' = 0 := fun W hW => by
    rw [hf', smul_eq_algebraMap_mul]
    exact ord_const_mul_mul_zpow_eq_zero hC0 hf hGf0 (hford W hW) (hGord W hW) (-n)

  refine ⟨n, (c₀ * ((q : ℕ) : AlgebraicClosure ℚ) ^ m₀)⁻¹, inv_ne_zero hC0, ?_⟩
  intro W hW
  obtain ⟨hmemA, hunitA⟩ :=
    ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed red hker ha hq f' hmem₁' hres₁' hmem₂'
      hres₂' hford' W hW
  have hWr : W.IsRational := isRational_place_modularFunctionFieldBar' (1 * q) W
  have heval : W.evalAt f * ((c₀ * ((q : ℕ) : AlgebraicClosure ℚ) ^ m₀)⁻¹)⁻¹ * (W.evalAt Gf) ^ (-n) = W.evalAt f' := by
    rw [inv_inv, hGfeq, hf', smul_eq_algebraMap_mul,
      evalAt_const_mul_mul_zpow hWr hC0 hf hGf0 (hford W hW) (hGord W hW) (-n)]
    ring
  rw [heval]
  exact ⟨hmemA, hunitA⟩

#print axioms solution

end S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation (solution)
