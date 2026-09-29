-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_zero_width_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5e787d47-339b-58f5-872b-966df23e22c5

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_exists_numberField_presentation
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_zero
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
import Theorems.Thm_ModularCurve_CharPReduction_exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
import Theorems.Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_zero_width_dvd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_zero_width_dvd.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_zero_width_dvd.ModularCurve.NodeLocalized"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.redRes CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full jWidth frickeInvolutionBar modularFunctionFieldBar ssJSet exists_numberField_presentation exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_zero NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg CharPReduction.exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP NodeLocalized.exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"

section Remint

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffMap_jqModC' (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

end Remint

section Bridges

private theorem coeffEmb_jq' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
  coeffMap_jqModC' (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coeffEmb_jqN' (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  have h := coeffMap_qExpand' (algebraMap ℚ (AlgebraicClosure ℚ)) N jq
  rw [jqNModC, ← coeffEmb_jq']
  exact h

end Bridges

namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver exists_gaussCoordinate_of_crossingPresentation_zero modularEvalAt isUnit_modularEvalAt coeffSubring_eq_or_isDiscreteValuationRing mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation modularRedLocHom_eq_zero_iff_mem_span_branchFst exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar pointEval_eq_zero_of_modularEval_eq_zero isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve.NodeLocalized"

section Helpers

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] (red : A →+* k)

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

end Helpers

section Legs

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] {red : A →+* k}
variable {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

private theorem modularEval_mem_bar (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ modularFunctionFieldBar (1 * q) := by
  have hj0 : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← coeffEmb_jq']
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))
  have hj1 : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← coeffEmb_jqN']
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp [modularEval, CharPReduction.constSeries]
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | mul_X p i h =>
    rw [map_mul]
    refine mul_mem h ?_
    fin_cases i
    · simpa [modularEval] using hj0
    · simpa [modularEval] using hj1

private theorem lift_leg {a : k}
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := by
  obtain ⟨r, t, ht, hf⟩ := f.2
  have hEt : modularEval (1 * q) (coeffSubring A K) t ≠ 0 := fun h0 =>
    ht (pointEval_eq_zero_of_modularEval_eq_zero red a K t h0)
  have hdiv : (f : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) t := by
    rw [eq_div_iff hEt]
    exact hf
  rw [hdiv]
  exact div_mem (modularEval_mem_bar r) (modularEval_mem_bar t)

private theorem modularEval_mem_modularRing (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ CharPReduction.modularRing (1 * q) A.toSubring := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hc : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c)
        = CharPReduction.constSeries A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2.1⟩ := by
      simp [modularEval, CharPReduction.constSeries]
    rw [hc]
    exact CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring _
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | mul_X p i h =>
    rw [map_mul]
    refine mul_mem h ?_
    fin_cases i
    · simpa [modularEval] using CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring
    · simpa [modularEval] using CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring

private theorem modularEval_notMem_redKer [DecidableEq k] [FiniteDimensional ℚ K] {a : k}
    (ha2 : a ^ (q ^ 2) = a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    {t : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (ht : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0) :
    (⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩ :
        ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉
      CharPReduction.redKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) := by
  intro hmem

  have hz : CharPReduction.modularRedLocHom (1 * q) A.toSubring red
      ⟨_, CharPReduction.subring_le_localizedAtKer A.toSubring red
        (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        (⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩ :
          ↥(CharPReduction.modularRing (1 * q) A.toSubring)).2⟩ = 0 := by
    show CharPReduction.redLocHom _ = 0
    rw [CharPReduction.redLocHom_apply]
    exact (CharPReduction.redLoc_coe (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing (1 * q) A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩).trans
      (RingHom.mem_ker.mp hmem)

  have hspan := (ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red a ha2 K ϖ hϖ
    ⟨_, modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) t⟩
    _).mp hz

  obtain ⟨-, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hloc
  have hmax' : IsLocalRing.maximalIdeal
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = _ := hmax
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (MvPolynomial.C x) q
  have hpoly : (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K))
      = (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)) - (MvPolynomial.X 0 - MvPolynomial.C x) * c := by
    rw [← hc, MvPolynomial.C_pow]
    ring
  have hle : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}
      ≤ IsLocalRing.maximalIdeal
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    rw [Ideal.span_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have h1 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have h2 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have h3 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have hsplit : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
          - (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) * (⟨modularEval (1 * q) (coeffSubring A K) (c), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      apply Subtype.ext
      show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
        = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))
          - modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x) * modularEval (1 * q) (coeffSubring A K) c
      rw [hpoly, map_sub, map_mul]
    rcases hy with rfl | rfl
    · exact h1
    · rw [hsplit]
      exact Ideal.sub_mem _ h3 (Ideal.mul_mem_right _ _ h2)

  haveI : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun p hp => RingHom.mem_ker.mpr
      (pointEval_eq_zero_of_modularEval_eq_zero red a K p (RingHom.mem_ker.mp hp))⟩
  have hu := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ht
  exact (IsLocalRing.mem_maximalIdeal _).mp (hle hspan) hu

private theorem mem_leg [DecidableEq k] [FiniteDimensional ℚ K] {a : k}
    (ha2 : a ^ (q ^ 2) = a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  obtain ⟨r, t, ht, hf⟩ := f.2
  exact ⟨⟨_, modularEval_mem_modularRing r⟩, ⟨_, modularEval_mem_modularRing t⟩,
    modularEval_notMem_redKer ha2 x hx ϖ hϖ ht, hf⟩

private theorem mem_leg₀ [DecidableEq k] [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
  mem_leg (zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)) 0 (map_zero _) ϖ hϖ f

omit [CharP k q] in

private theorem notMem_of_isUnit {x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))} (hx : IsUnit x) {I : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))} (hI : I.IsPrime) : x ∉ I :=
  fun h => hI.ne_top (Ideal.eq_top_of_isUnit_mem I h hx)

private theorem infty_leg [DecidableEq k] [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hx : x ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))}) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, mem_leg₀ ϖ hϖ x⟩ ≠ 0 := by
  intro h0
  exact hx ((ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red (0 : k)
    (zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)) K ϖ hϖ x (mem_leg₀ ϖ hϖ x)).mp h0)

omit [CharP k q] in

private theorem scaled_unit_leg [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK) (e : ℕ)
    (X Y Wm : ↥(modularFunctionFieldBar (1 * q)))
    (hXY : (X : LaurentSeries (AlgebraicClosure ℚ)) * (Y : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) * (Wm : LaurentSeries (AlgebraicClosure ℚ)))
    (hWO : (Wm : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) (hπW : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hWO⟩ ≠ 0)
    (hYO : (Y : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) (hπY : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hYO⟩ ≠ 0) :
    ∃ hX₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • X : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hX₁⟩ ≠ 0 := by
  obtain ⟨εu, hεu⟩ := hε
  set ε' : ↥(coeffSubring A K) := ((εu⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) with hε'
  have hεε' : ε * ε' = 1 := by
    rw [hε', ← hεu]
    exact εu.mul_inv
  have hconst : ∀ c : ↥(coeffSubring A K), algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    fun c => CharPReduction.subring_le_localizedAtKer A.toSubring red _ _
      (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2.1⟩)
  have hcε' : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [map_pow]
    exact pow_mem (hconst ε') e
  have hcε : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε : AlgebraicClosure ℚ) ^ e) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [map_pow]
    exact pow_mem (hconst ε) e
  have hεε'L : (ε : AlgebraicClosure ℚ) * (ε' : AlgebraicClosure ℚ) = 1 := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hεε'
    simpa using h
  have hπcε' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hcε'⟩ ≠ 0 := by
    have hone : (⟨_, hcε'⟩ * ⟨_, hcε⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 := by
      apply Subtype.ext
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε : AlgebraicClosure ℚ) ^ e) = 1
      rw [← map_mul, ← mul_pow, mul_comm, hεε'L, one_pow, map_one]
    have h := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hone
    rw [map_mul, map_one] at h
    exact left_ne_zero_of_mul_eq_one h
  obtain ⟨hYiO, hπYi⟩ := exists_inv_mem_modularLocalized red hYO hπY
  have hπYi' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hYiO⟩ ≠ 0 := by
    rw [hπYi]
    exact inv_ne_zero hπY
  have hYL : (Y : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := ne_zero_of_modularRedLocHom_ne_zero red hYO hπY
  have hqL : (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqϖL : ((q : ℕ) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simpa using h
  have hT : (((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • X : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) * (Wm : LaurentSeries (AlgebraicClosure ℚ)) * ((Y⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hYinv : ((Y⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (Y : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by norm_cast
    rw [hYinv, IntermediateField.coe_smul, Algebra.smul_def, map_inv₀, map_pow, hqϖL, map_mul, map_pow, map_pow]
    have hεL : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε : AlgebraicClosure ℚ) * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε' : AlgebraicClosure ℚ) = 1 := by
      rw [← map_mul, hεε'L, map_one]
    have hϖL : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ)) ^ (e * eK) := map_pow _ _ _
    rw [hϖL] at hXY
    have hϖne : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply hqL
      rw [hqϖL]
      have : (ϖ : AlgebraicClosure ℚ) = 0 := (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h0
      rw [this, zero_pow (by omega), zero_mul]
    have hEinv : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε : AlgebraicClosure ℚ))⁻¹ = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε' : AlgebraicClosure ℚ) :=
      inv_eq_of_mul_eq_one_right hεL
    rw [← hEinv, eq_mul_inv_iff_mul_eq₀ hYL, mul_assoc, hXY, mul_pow, ← pow_mul, mul_comm eK e, mul_inv, inv_pow,
      mul_comm ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ)) ^ (e * eK))⁻¹, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖne)]
  have hX₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • X : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hT]
    exact mul_mem (mul_mem hcε' hWO) hYiO
  refine ⟨hX₁, ?_⟩
  have hsplit : (⟨_, hX₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hcε'⟩ * ⟨_, hWO⟩ * ⟨_, hYiO⟩ := by
    apply Subtype.ext
    exact hT
  rw [hsplit, map_mul, map_mul]
  exact mul_ne_zero (mul_ne_zero hπcε' hπW) hπYi'

private theorem fricke_leg [DecidableEq k] [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (x H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) (hxF : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'}
      = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (hx : x ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'}) :
    ∃ hG₂ : ((frickeInvolutionBar (1 * q) (⟨(x : LaurentSeries (AlgebraicClosure ℚ)), hxF⟩ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₂⟩ ≠ 0 := by
  set xm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)), hxF⟩ with hxm

  have hq0 : ((0 : k) ^ q) = 0 := zero_pow (Fact.out : q.Prime).ne_zero
  have ha2₀ : (0 : k) ^ (q ^ 2) = 0 := zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)
  obtain ⟨σ, hσcoe, hσeval⟩ :=
    ModularCurve.NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar red (0 : k) ha2₀ K

  have ha2' : ((0 : k) ^ q) ^ (q ^ 2) = (0 : k) ^ q := by rw [hq0, ha2₀]
  have hx' : redRestrict red K 0 = (0 : k) ^ q := by rw [map_zero, hq0]
  have hσx : ((σ x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q) xm : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := hσcoe x hxF
  have hfrx : ((frickeInvolutionBar (1 * q) xm : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [← hσx]
    exact mem_leg ha2' 0 hx' ϖ hϖ (σ x)
  have hσxO : ((σ x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hσx]
    exact hfrx
  have hredFrx : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hfrx⟩ ≠ 0 := by
    intro h0
    have h0' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hσxO⟩ = 0 := by
      have hEq : (⟨_, hσxO⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hfrx⟩ := Subtype.ext hσx
      rw [hEq]
      exact h0
    have hmemσ := (ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red ((0 : k) ^ q) ha2' K ϖ hϖ
      (σ x) hσxO).mp h0'

    have himg : Ideal.map (σ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q)))
        (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
        = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((0 : k) ^ q) (((0 : k) ^ q) ^ q)))} := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      have e1 := hσeval (MvPolynomial.C ϖ)
      have e2 := hσeval (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
      have hrenC : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.C ϖ : MvPolynomial (Fin 2) ↥(coeffSubring A K))
          = MvPolynomial.C ϖ := MvPolynomial.rename_C _ _
      have hrenX : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
            (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K))
          = MvPolynomial.X 1 - MvPolynomial.X 0 ^ q := by
        simp [MvPolynomial.rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hrenC] at e1
      rw [hrenX] at e2
      simp only [RingHom.coe_coe]
      rw [show (σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))) = σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) (MvPolynomial.C ϖ)) from rfl,
        show (σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))) = σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) from rfl,
        e1, e2]
      rfl
    rw [← himg] at hmemσ
    obtain ⟨g₀, hg₀, hg₀eq⟩ := (Ideal.mem_map_of_equiv σ _).mp hmemσ
    have hg₀x : g₀ = x := σ.injective hg₀eq
    rw [hg₀x, ← hsp2] at hg₀
    exact hx hg₀
  exact ⟨hfrx, hredFrx⟩

end Legs

end NodeLocalized
end ModularCurve

private theorem exists_generator_ker_redRestrict' {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by

  have hU : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ¬ IsUnit c := by
    intro c
    have hred : redRestrict red K c = red ⟨(c : AlgebraicClosure ℚ), c.2.1⟩ := rfl
    rw [hred, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hnu hu
      apply hnu
      exact hu.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring))
    · intro hnu hu
      apply hnu
      obtain ⟨v, hv⟩ := hu
      have hmul : ((v : A) : AlgebraicClosure ℚ) * (((v⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
        have h := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) v.mul_inv
        push_cast at h
        exact h
      have hcv : ((v : A) : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ) := by rw [hv]
      rw [hcv] at hmul
      have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hmul
      have hwK : (((v⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) ∈ K := by
        rw [eq_inv_of_mul_eq_one_right hmul]
        exact K.inv_mem c.2.2
      refine isUnit_iff_exists_inv.mpr ⟨⟨(((v⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ), ⟨((v⁻¹ : Aˣ) : A).2, hwK⟩⟩, Subtype.ext ?_⟩
      exact hmul
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with heq | hdvr
  ·
    refine ⟨0, fun c => ?_⟩
    rw [hU]
    constructor
    · intro hnu
      refine ⟨0, ?_⟩
      rw [mul_zero]
      by_contra hc0
      apply hnu
      have hc0' : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hcK : (c : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K :=
        (SetLike.ext_iff.mp heq ((c : AlgebraicClosure ℚ)⁻¹)).mpr (K.inv_mem c.2.2)
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hcK⟩, Subtype.ext ?_⟩
      show (c : AlgebraicClosure ℚ) * (c : AlgebraicClosure ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ hc0'
    · rintro ⟨d, hd⟩
      rw [hd, zero_mul]
      exact not_isUnit_zero
  ·
    haveI := hdvr
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    refine ⟨ϖ, fun c => ?_⟩
    rw [hU, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Iff.rfl

private theorem const_mem_O
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    (a : A) : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
  CharPReduction.subring_le_localizedAtKer A.toSubring red _ _
    (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩)

private theorem smul_eq_algebraMap_mul {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    c • x = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c * x :=
  Algebra.smul_def c x

private theorem smul_eq_algebraMap_mul' {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    c • x = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c * x := by
  apply Subtype.ext
  push_cast
  exact Algebra.smul_def c (x : LaurentSeries (AlgebraicClosure ℚ))

private theorem fricke_smul {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) (c • x) = c • frickeInvolutionBar (1 * q) x := by
  rw [smul_eq_algebraMap_mul, map_mul, AlgEquiv.commutes, ← smul_eq_algebraMap_mul]

private theorem smul_smul' {q : ℕ} [Fact q.Prime] (a b : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) : a • (b • x) = (a * b) • x := by
  rw [smul_eq_algebraMap_mul, smul_eq_algebraMap_mul, smul_eq_algebraMap_mul, map_mul, mul_assoc]

private theorem smul_mem_O
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    (a : A) (x : ↥(modularFunctionFieldBar (1 * q)))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    (((a : AlgebraicClosure ℚ) • x : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]
  exact mul_mem (const_mem_O red a) hx

private theorem scaling_leg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red ∧
      ((frickeInvolutionBar (1 * q) (c • f) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  obtain ⟨c₁, hc₁, h₁, -⟩ :=
    CharPReduction.exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP red f hf
  have hff : frickeInvolutionBar (1 * q) f ≠ 0 := fun h => hf ((frickeInvolutionBar (1 * q)).injective (by rw [h, map_zero]))
  obtain ⟨c₂, hc₂, h₂, -⟩ :=
    CharPReduction.exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP red (frickeInvolutionBar (1 * q) f) hff
  rcases A.mem_or_inv_mem (c₂ / c₁) with hA | hA
  · refine ⟨c₂, hc₂, ?_, ?_⟩
    · have h := smul_mem_O red ⟨c₂ / c₁, hA⟩ (c₁ • f) h₁
      rwa [smul_smul', div_mul_cancel₀ c₂ hc₁] at h
    · rw [fricke_smul]
      exact h₂
  · refine ⟨c₁, hc₁, h₁, ?_⟩
    rw [fricke_smul]
    have hA' : c₁ / c₂ ∈ A := by rwa [inv_div] at hA
    have h := smul_mem_O red ⟨c₁ / c₂, hA'⟩ (c₂ • frickeInvolutionBar (1 * q) f) h₂
    rwa [smul_smul', div_mul_cancel₀ c₁ hc₂] at h

private theorem modularEval_mem_fieldOver
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (P : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) P ∈ fieldOver (1 * q) K := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    apply Subfield.subset_closure
    refine Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, ?_⟩
    simp [modularEval, CharPReduction.constSeries]
    rfl
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | mul_X p n h =>
    rw [map_mul]
    refine mul_mem h ?_
    apply Subfield.subset_closure
    fin_cases n
    · exact Or.inr (by simp [modularEval])
    · exact Or.inr (by simp [modularEval])

private theorem fieldOver_leg
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (f : ↥(modularFunctionFieldBar (1 * q))) (P Q : MvPolynomial (Fin 2) (coeffSubring A K))
    (hQ : modularEval (1 * q) (coeffSubring A K) Q ≠ 0)
    (hPQ : (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) Q = modularEval (1 * q) (coeffSubring A K) P) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K := by
  have : (f : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) P / modularEval (1 * q) (coeffSubring A K) Q :=
    (eq_div_iff hQ).mpr hPQ
  rw [this]
  exact div_mem (modularEval_mem_fieldOver A K P) (modularEval_mem_fieldOver A K Q)

private theorem ord_smul_const
    {q : ℕ} [Fact q.Prime] (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) : W.ord (c • f) = W.ord f := by
  have hc' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c ≠ 0 := (map_ne_zero _).mpr hc
  rw [smul_eq_algebraMap_mul, W.ord_mul hc' hf, StandardAnnulus.ord_algebraMap_eq_zero W hc, zero_add]

private theorem scalar_identity₁ {F : Type*} [Field F] (φ : AlgebraicClosure ℚ →+* F) (P Q : AlgebraicClosure ℚ) (hP : φ P ≠ 0) (hQ : φ Q ≠ 0)
    (H G U : F) (l i j : ℕ) :
    φ ((P ^ l)⁻¹ * (Q ^ j)⁻¹) * (φ P ^ l * H ^ i * G ^ j * U) = H ^ i * (φ Q⁻¹ * G) ^ j * U := by
  have hPl : (φ P ^ l)⁻¹ * φ P ^ l = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  have _ := hQ
  simp only [map_mul, map_inv₀, map_pow]
  linear_combination ((φ Q ^ j)⁻¹ * (H ^ i * G ^ j * U)) * hPl

private theorem scalar_identity₂ {F : Type*} [Field F] (φ : AlgebraicClosure ℚ →+* F) (P Q : AlgebraicClosure ℚ) (hP : φ P ≠ 0) (hQ : φ Q ≠ 0)
    (H G U : F) (l i j : ℕ) :
    φ ((P ^ l)⁻¹ * (Q ^ i)⁻¹) * (φ P ^ l * H ^ i * G ^ j * U) = (φ Q⁻¹ * H) ^ i * G ^ j * U := by
  have hPl : (φ P ^ l)⁻¹ * φ P ^ l = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  have _ := hQ
  simp only [map_mul, map_inv₀, map_pow]
  linear_combination ((φ Q ^ i)⁻¹ * (H ^ i * G ^ j * U)) * hPl

private theorem ends_leg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (0 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    [IsAlgClosed k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ (jWidth (0 : k) * eK) * w)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (f : ↥(modularFunctionFieldBar (1 * q))) (c₀ : AlgebraicClosure ℚ) (hc₀ : c₀ ≠ 0) (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = ((c₀ • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))
    (l i j : ℕ) (u : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) (hu : IsUnit u)
    (hfac : g = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ l * H' ^ i * G' ^ j * u) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (m : ℤ) (_ : ((jWidth (0 : k) : ℕ) : ℤ) ∣ m)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 := by

  obtain ⟨Gf, hGfeq, hG₁, hG₂, hπG₁, hπG₂, -⟩ :=
    ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_zero red hker ha hq K ϖ hϖ eK ε hε hqϖ heK1
      G' H' w hw hGH hpr1 hpr2 hnm1 hnm2 hsp1 hsp2
  have hHF : (H' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg H'
  have hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg G'
  have hwF : (w : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg w
  have huF : (u : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg u
  have hGfm : Gf = (⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ : ↥(modularFunctionFieldBar (1 * q))) := Subtype.ext hGfeq

  have hHO : (H' : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ H'
  have hπH : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hHO⟩ ≠ 0 := by
    apply infty_leg ϖ hϖ H'
    rw [← hsp1]
    exact hnm1
  have huO : (u : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ u
  have hπu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, huO⟩ ≠ 0 := by
    apply infty_leg ϖ hϖ u
    rw [← hsp1]
    exact notMem_of_isUnit hu hpr1

  obtain ⟨hfw, hπfw⟩ := fricke_leg ϖ hϖ w H' hwF hsp2 (notMem_of_isUnit hw hpr2)
  obtain ⟨hfu, hπfu⟩ := fricke_leg ϖ hϖ u H' huF hsp2 (notMem_of_isUnit hu hpr2)
  have hqL : (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqϖL : ((q : ℕ) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simpa using h
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hqL
    rw [hqϖL, h0, zero_pow (by omega), zero_mul]
  have hGHL : (G' : LaurentSeries (AlgebraicClosure ℚ)) * (H' : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (jWidth (0 : k) * eK)) * (w : LaurentSeries (AlgebraicClosure ℚ)) := by
    have h := congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) hGH
    simpa [modularEval, CharPReduction.constSeries, map_pow] using h
  have hGHm : Gf * (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : AlgebraicClosure ℚ) ^ (jWidth (0 : k) * eK)) * (⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ : ↥(modularFunctionFieldBar (1 * q))) := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, hGfeq]
    exact hGHL
  have hXYm : frickeInvolutionBar (1 * q) (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q))) * frickeInvolutionBar (1 * q) Gf = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : AlgebraicClosure ℚ) ^ (jWidth (0 : k) * eK)) * frickeInvolutionBar (1 * q) (⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [← map_mul, mul_comm ((⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q)))) Gf, hGHm, map_mul, AlgEquiv.commutes]
  have hXY : ((frickeInvolutionBar (1 * q) (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * ((frickeInvolutionBar (1 * q) Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (jWidth (0 : k) * eK)) * ((frickeInvolutionBar (1 * q) (⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← IntermediateField.coe_mul, hXYm, IntermediateField.coe_mul]
    rfl
  obtain ⟨hfH, hπfH⟩ := scaled_unit_leg ϖ eK ε hε hqϖ heK1 (jWidth (0 : k)) (frickeInvolutionBar (1 * q) (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q)))) (frickeInvolutionBar (1 * q) Gf) (frickeInvolutionBar (1 * q) (⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ : ↥(modularFunctionFieldBar (1 * q)))) hXY hfw hπfw hG₂ hπG₂

  have hcf : c₀ • f = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ϖ : AlgebraicClosure ℚ) ^ l * (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q))) ^ i * (⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ : ↥(modularFunctionFieldBar (1 * q))) ^ j * (⟨(u : LaurentSeries (AlgebraicClosure ℚ)), huF⟩ : ↥(modularFunctionFieldBar (1 * q))) := by
    apply Subtype.ext
    rw [← hg, hfac]
    push_cast
    simp [modularEval, CharPReduction.constSeries]
  have hP0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ϖ : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hQ0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ≠ 0 := (map_ne_zero _).mpr (pow_ne_zero _ hqL)
  have hI : ((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) • f = (((⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q)))) ^ i * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k))⁻¹ • Gf) ^ j *
      (⟨(u : LaurentSeries (AlgebraicClosure ℚ)), huF⟩ : ↥(modularFunctionFieldBar (1 * q)))) := by
    rw [← smul_smul', hcf, hGfm, smul_eq_algebraMap_mul, smul_eq_algebraMap_mul]
    exact scalar_identity₁ _ _ _ hP0 hQ0 _ _ _ l i j
  have hqm : ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) = (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j / (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ i := by
    rw [zpow_mul, zpow_natCast, zpow_sub₀ (pow_ne_zero _ hqL), zpow_natCast, zpow_natCast]
  have hsc : ((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) = ((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ i)⁻¹) * c₀) := by
    rw [hqm]
    have hQ : (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ≠ 0 := pow_ne_zero _ hqL
    field_simp
  have hII : (((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ)))) • f = (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k))⁻¹ • (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q)))) ^ i * Gf ^ j *
      (⟨(u : LaurentSeries (AlgebraicClosure ℚ)), huF⟩ : ↥(modularFunctionFieldBar (1 * q)))) := by
    rw [hsc, ← smul_smul', hcf, hGfm, smul_eq_algebraMap_mul, smul_eq_algebraMap_mul]
    exact scalar_identity₂ _ _ _ hP0 hQ0 _ _ _ l i j

  have h₁ : ((((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hI, IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_pow]
    exact mul_mem (mul_mem (pow_mem hHO i) (pow_mem hG₁ j)) huO
  have hπ₁ : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
    have hsplit : (⟨_, h₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hHO⟩ ^ i * ⟨_, hG₁⟩ ^ j * ⟨_, huO⟩ := by
      apply Subtype.ext
      show ((((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
      rw [hI]
      push_cast
      rfl
    rw [hsplit, map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπH) (pow_ne_zero _ hπG₁)) hπu
  have hfrII : frickeInvolutionBar (1 * q) ((((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ)))) • f)
      = ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k))⁻¹ • frickeInvolutionBar (1 * q) (⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : ↥(modularFunctionFieldBar (1 * q)))) ^ i * (frickeInvolutionBar (1 * q) Gf) ^ j * frickeInvolutionBar (1 * q) (⟨(u : LaurentSeries (AlgebraicClosure ℚ)), huF⟩ : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [hII, map_mul, map_mul, map_pow, map_pow, fricke_smul]
  have h₂ : ((frickeInvolutionBar (1 * q) ((((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ)))) • f) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hfrII, IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_pow]
    exact mul_mem (mul_mem (pow_mem hfH i) (pow_mem hG₂ j)) hfu
  have hπ₂ : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 := by
    have hsplit : (⟨_, h₂⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hfH⟩ ^ i * ⟨_, hG₂⟩ ^ j * ⟨_, hfu⟩ := by
      apply Subtype.ext
      show ((frickeInvolutionBar (1 * q) ((((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ)))) • f) : ↥(modularFunctionFieldBar (1 * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) = _
      rw [hfrII]
      push_cast
      rfl
    rw [hsplit, map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπfH) (pow_ne_zero _ hπG₂)) hπfu
  have hc : ((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hϖ0)) (inv_ne_zero (pow_ne_zero _ (pow_ne_zero _ hqL)))) hc₀
  exact ⟨((((ϖ : AlgebraicClosure ℚ) ^ l)⁻¹ * ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k)) ^ j)⁻¹) * c₀), hc, ((jWidth (0 : k) : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ)), dvd_mul_right _ _, h₁, h₂, hπ₁, hπ₂⟩

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (0 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (m : ℤ) (_ : ((jWidth (0 : k) : ℕ) : ℤ) ∣ m)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 := by

  obtain ⟨c₀, hc₀, h₁, h₂⟩ := scaling_leg red f hf

  obtain ⟨K, fdK, P, Q, hQ, hPQ⟩ := ModularCurve.exists_numberField_presentation A (c₀ • f)
  haveI := fdK
  have hfK : ((c₀ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K :=
    fieldOver_leg A K (c₀ • f) P Q hQ hPQ
  obtain ⟨ϖ, hϖ⟩ := exists_generator_ker_redRestrict' red hker K
  obtain ⟨eK, ε, heK1, hε, hqϖ, G', H', w, hw, hGH, hmax, hpr1, hpr2, hnm1, hnm2, hsp1, hsp2⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring red (0 : k) ha
      (zero_pow (pow_ne_zero 2 (Fact.out (p := Nat.Prime q)).ne_zero)) hq K 0 (map_zero _) ϖ hϖ
  have hford' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
      W.ord (c₀ • f) = 0 := by
    intro W hW
    rw [ord_smul_const W c₀ hc₀ f hf]
    exact hford W hW
  have hmem := ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg red hq (0 : k) ha (zero_pow (pow_ne_zero 2 (Fact.out (p := Nat.Prime q)).ne_zero)) (c₀ • f) h₁ h₂ (fun W hW => (hford' W hW).ge) K 0 (map_zero _) hfK
  set g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)) := ⟨_, hmem⟩ with hgdef
  have hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = ((c₀ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := rfl
  have hg0 : g ≠ 0 := by
    intro h0
    have h : ((c₀ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      rw [← hg]
      simp [h0]
    have h' : (c₀ • f : ↥(modularFunctionFieldBar (1 * q))) = 0 := Subtype.ext h
    rw [smul_eq_algebraMap_mul] at h'
    rcases mul_eq_zero.mp h' with h0c | h0f
    · exact (map_ne_zero _).mpr hc₀ h0c
    · exact hf h0f
  have hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [hg]
    exact (c₀ • f).2
  obtain ⟨l, i, j, u, hu, hfac⟩ :=
    ModularCurve.NodeLocalized.exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation red (0 : k) (zero_pow (pow_ne_zero 2 (Fact.out (p := Nat.Prime q)).ne_zero)) K 0 (map_zero _) ϖ hϖ eK ε heK1 hε hqϖ G' H' w hw hGH hmax hpr1 hpr2 hnm1 hnm2
      hsp1 hsp2 g hg0 hgF (by
        have hge : (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) = c₀ • f := Subtype.ext hg
        rw [hge]
        exact hford')
  exact ends_leg red hker ha hq K ϖ hϖ eK ε hε hqϖ heK1 G' H' w hw hGH hpr1 hpr2 hnm1 hnm2 hsp1 hsp2 f c₀ hc₀ g hg l i j u hu hfac

section Probes
#print axioms solution
end Probes

end S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_zero_width_dvd
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_zero_width_dvd (solution)
