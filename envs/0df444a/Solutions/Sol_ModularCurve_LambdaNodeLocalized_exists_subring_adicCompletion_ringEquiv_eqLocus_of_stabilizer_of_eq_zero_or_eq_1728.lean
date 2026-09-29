-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fcfaa52d-f17b-5410-a5b4-ccd0fdb11f9b

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal
import Definitions.Def_InvariantsCompletion
import Definitions.Def_PolynomialCompletion
import Definitions.Def_AdicCompletionRingFunctoriality
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint
import Theorems.Thm_AdicCompletion_ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing
import Theorems.Thm_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint
import Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve"
namespace Ws35FIXA

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

abbrev R₀ : Subring LQ :=
  modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)

abbrev ev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(R₀ q A red a K) :=
  ⟨modularEval (1 * q) (coeffSubring A K) p,
    modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p⟩

end Defs

section FieldFacts
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

theorem const_mem_fieldOver (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inl ⟨⟨(c : Qb), c.2.2⟩, rfl⟩)

theorem const_mem_lambdaFieldOver (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ lambdaFieldOver q K :=
  Subfield.subset_closure (Or.inl ⟨⟨(c : Qb), c.2.2⟩, rfl⟩)

theorem modularEval_mem_fieldOver (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ fieldOver (1 * q) K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact const_mem_fieldOver q A K c
  | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    fin_cases i
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem lambdaEval_mem_lambdaFieldOver (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    lambdaEval q (coeffSubring A K) p ∈ lambdaFieldOver q K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact const_mem_lambdaFieldOver q A K c
  | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    fin_cases i
    · exact lambdaModC_mem_lambdaFieldOver q K
    · exact lambdaNModC_mem_lambdaFieldOver q K

theorem R₀_le_fieldOver [CharP k q] : R₀ q A red a K ≤ (fieldOver (1 * q) K).toSubring := by
  rintro f ⟨r, s, hs, hfs⟩
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h0 =>
    hs (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s h0)
  have : f = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) s := by
    rw [eq_div_iff hs0, hfs]
  rw [Subfield.mem_toSubring, this]
  exact div_mem (modularEval_mem_fieldOver q A K r) (modularEval_mem_fieldOver q A K s)

omit [Fact q.Prime] in

theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

omit [Fact q.Prime] in

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) (jLambda_Qb)
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

end FieldFacts

end Ws35FIXA
end ModularCurve

end

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section KorbBlock
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"
open scoped Pointwise
namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
namespace Ws35FIXA
p2m_open "ModularCurve"

theorem mem_rootFinset_of_level_two_value
    {k : Type*} [Field k] [DecidableEq k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (l' : k) (hla' : a * ((16 * l') ^ 2 * (16 * l' - 1) ^ 2) = 256 * ((16 * l') ^ 2 - 16 * l' + 1) ^ 3) :
    l' ∈ (if a = 0 then ({l, 16⁻¹ - l} : Finset k) else {-16⁻¹, 8⁻¹, 32⁻¹}) := by

  have hqP : q.Prime := Fact.out
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k q 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h3 : (3 : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k q 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have h256 : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  rcases h01728 with rfl | rfl
  ·
    simp only [↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
    have hQ : ∀ t : k, 0 * ((16 * t) ^ 2 * (16 * t - 1) ^ 2) = 256 * ((16 * t) ^ 2 - 16 * t + 1) ^ 3 →
        (16 * t) ^ 2 - 16 * t + 1 = 0 := by
      intro t ht
      rw [zero_mul] at ht
      have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp ht.symm).resolve_left h256)
      exact this
    have hl0 := hQ l hla
    have hl'0 := hQ l' hla'

    have hdiff : (16 : k) * (l' - l) * (16 * (l' + l) - 1) = 0 := by
      have : (16 : k) * (l' - l) * (16 * (l' + l) - 1) = ((16 * l') ^ 2 - 16 * l' + 1) - ((16 * l) ^ 2 - 16 * l + 1) := by
        ring
      rw [this, hl0, hl'0, sub_zero]
    rcases mul_eq_zero.mp hdiff with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h h16
      · exact Or.inl (sub_eq_zero.mp h)
    · right
      have : l' + l = 16⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination h)
      linear_combination this
  ·
    have h1728 : (1728 : k) ≠ 0 := by
      have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
      rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    simp only [h1728, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
    have key : (64 : k) * ((16 * l' + 1) ^ 2 * (16 * l' - 2) ^ 2 * (2 * (16 * l') - 1) ^ 2) = 0 := by
      have : (64 : k) * ((16 * l' + 1) ^ 2 * (16 * l' - 2) ^ 2 * (2 * (16 * l') - 1) ^ 2)
          = 256 * ((16 * l') ^ 2 - 16 * l' + 1) ^ 3 - 1728 * ((16 * l') ^ 2 * (16 * l' - 1) ^ 2) := by ring
      rw [this, ← hla', sub_self]
    have h64 : (64 : k) ≠ 0 := by
      have : (64 : k) = 2 ^ 6 := by norm_num
      rw [this]; exact pow_ne_zero _ h2
    have := (mul_eq_zero.mp key).resolve_left h64
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left
        have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        rw [neg_inv]
        exact eq_inv_of_mul_eq_one_left (by linear_combination -h')
      · right; left
        have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        have h'' : (2 : k) * (l' * 8 - 1) = 0 := by linear_combination h'
        exact eq_inv_of_mul_eq_one_left (sub_eq_zero.mp ((mul_eq_zero.mp h'').resolve_left h2))
    · right; right
      have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      exact eq_inv_of_mul_eq_one_left (by linear_combination h')

theorem card_rootFinset_le
    {k : Type*} [Field k] [DecidableEq k] (a l : k) :
    (if a = 0 then ({l, 16⁻¹ - l} : Finset k) else {-16⁻¹, 8⁻¹, 32⁻¹}).card ≤ (if a = 0 then 2 else 3) := by
  split_ifs
  · exact Finset.card_le_two
  · exact (Finset.card_le_three)

theorem isUnit_subring_iff {F : Type*} [Field F] (S : Subring F) (x : ↥S) :
    IsUnit x ↔ (x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ S := by
  constructor
  · rintro ⟨u, rfl⟩
    have hne : ((u : ↥S) : F) ≠ 0 := by
      intro h
      have : ((u * u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by rw [mul_inv_cancel]; rfl
      have h1 : ((u : ↥S) : F) * ((u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by exact_mod_cast this
      rw [h, zero_mul] at h1; exact zero_ne_one h1
    refine ⟨hne, ?_⟩
    have : ((u : ↥S) : F)⁻¹ = ((u⁻¹ : (↥S)ˣ) : ↥S) := by
      have h1 : ((u : ↥S) : F) * ((u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by
        have : ((u * u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by rw [mul_inv_cancel]; rfl
        exact_mod_cast this
      exact (eq_inv_of_mul_eq_one_right h1).symm
    rw [this]; exact Subtype.coe_prop _
  · rintro ⟨hne, hinv⟩
    refine ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

theorem exists_smul_eq_of_isMaximal
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (B : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hB : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ B ↔
      z ∈ lambdaFieldOver q K ∧
        ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem z)
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (hBS : B ≤ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    (h𝔓max : ((IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS)).IsMaximal)
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G ↥B] (hcard : Fintype.card G = 6)
    (hstab : Nat.card (MulAction.stabilizer G
      ((IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS))) ≤ jWidth a)
    (Q : Ideal ↥B) (hQ : Q.IsMaximal) :
    ∃ γ : G, Q = γ • (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS) := by
  classical
  set 𝔓 : Ideal ↥B := (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS) with h𝔓
  have hqP : q.Prime := Fact.out
  have h2 : (2 : k) ≠ 0 := by
    intro h2
    have := (CharP.cast_eq_zero_iff k q 2).mp (by exact_mod_cast h2)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h3 : (3 : k) ≠ 0 := by
    intro h3
    have := (CharP.cast_eq_zero_iff k q 3).mp (by exact_mod_cast h3)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h1728 : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

  let R : Finset k := if a = 0 then ({l, 16⁻¹ - l} : Finset k) else {-16⁻¹, 8⁻¹, 32⁻¹}
  have hRe : R.card * jWidth a ≤ 6 := by
    rcases h01728 with h0 | h17
    · rw [jWidth_of_eq_zero h0]
      have : R.card ≤ 2 := by simp only [R, h0, ↓reduceIte]; exact Finset.card_le_two
      omega
    · have h0 : a ≠ 0 := by rw [h17]; exact h1728
      rw [jWidth_of_eq_1728 h17 h0]
      have : R.card ≤ 3 := by simp only [R, h0, ↓reduceIte]; exact Finset.card_le_three
      omega
  have hepos : 0 < jWidth a := jWidth_pos a

  let Mx := {P : Ideal ↥B // P.IsMaximal}
  have hORB : ∀ P : Mx, ∃ r : k, r ∈ R ∧ ∀ b : ↥B, b ∈ P.1 ↔
      ¬ ((b : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 ∧
          (b : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) r (r ^ q)) := by
    intro P
    obtain ⟨l', hla', y', hy', hBS', hloc', hP⟩ :=
      ModularCurve.LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal hq red a ha ha2 h01728 K ϖ hϖ l hla y hy B hB P.1 P.2
    refine ⟨l', mem_rootFinset_of_level_two_value hq a h01728 l hla l' hla', fun b => ?_⟩
    haveI := hloc'
    rw [hP, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_subring_iff]
    rfl
  choose ρ hρR hρmem using hORB
  have hρinj : Function.Injective ρ := by
    intro P₁ P₂ h
    apply Subtype.ext
    ext b
    rw [hρmem P₁ b, hρmem P₂ b, h]

  let ρ' : Mx → ↥R := fun P => ⟨ρ P, hρR P⟩
  have hρ'inj : Function.Injective ρ' := fun P₁ P₂ h => hρinj (congrArg Subtype.val h)
  haveI : Finite Mx := Finite.of_injective ρ' hρ'inj
  have hMxR : Nat.card Mx ≤ R.card := by
    have := Nat.card_le_card_of_injective ρ' hρ'inj
    rwa [Nat.card_eq_finsetCard] at this

  have hsmul_max : ∀ γ : G, (γ • 𝔓).IsMaximal := by
    intro γ
    haveI := h𝔓max
    refine ⟨⟨fun htop => h𝔓max.ne_top ?_, fun J hJ => ?_⟩⟩
    · have := congrArg (fun I : Ideal ↥B => γ⁻¹ • I) htop
      simp only [inv_smul_smul] at this
      rw [this, Ideal.pointwise_smul_def, Ideal.map_top]
    ·
      have hle : 𝔓 ≤ γ⁻¹ • J := by
        have := Ideal.map_mono (f := MulSemiringAction.toRingHom G (↥B) γ⁻¹) hJ.le
        rw [← Ideal.pointwise_smul_def, ← Ideal.pointwise_smul_def, inv_smul_smul] at this
        exact this
      have hne : 𝔓 ≠ γ⁻¹ • J := fun h => hJ.ne (by rw [h, smul_inv_smul])
      have h2 := h𝔓max.1.2 _ (lt_of_le_of_ne hle hne)
      have h3 : γ • (γ⁻¹ • J) = γ • (⊤ : Ideal ↥B) := congrArg _ h2
      rw [smul_inv_smul] at h3
      rw [h3, Ideal.pointwise_smul_def, Ideal.map_top]
  let O := MulAction.orbit G 𝔓
  let ι : ↥O → Mx := fun P => ⟨P.1, by obtain ⟨γ, hγ⟩ := P.2; rw [← hγ]; exact hsmul_max γ⟩
  have hιinj : Function.Injective ι := fun P₁ P₂ h => Subtype.ext (congrArg (fun x : Mx => x.1) h)
  haveI : Finite ↥O := Finite.of_injective ι hιinj
  have hOMx : Nat.card ↥O ≤ Nat.card Mx := Nat.card_le_card_of_injective ι hιinj

  haveI : Fintype ↥O := Fintype.ofFinite _
  have hOS : Nat.card ↥O * Nat.card (MulAction.stabilizer G 𝔓) = 6 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group, hcard]
  haveI : Nonempty ↥O := ⟨⟨𝔓, MulAction.mem_orbit_self 𝔓⟩⟩
  have hOpos : 0 < Nat.card ↥O := Nat.card_pos

  have hOeq : Nat.card Mx ≤ Nat.card ↥O := by
    have h1 : Nat.card Mx * jWidth a ≤ 6 := le_trans (Nat.mul_le_mul_right _ hMxR) hRe
    have h2 : 6 ≤ Nat.card ↥O * jWidth a := by
      calc 6 = Nat.card ↥O * Nat.card (MulAction.stabilizer G 𝔓) := hOS.symm
        _ ≤ Nat.card ↥O * jWidth a := Nat.mul_le_mul_left _ hstab
    exact Nat.le_of_mul_le_mul_right (le_trans h1 h2) hepos
  have hιbij : Function.Bijective ι := hιinj.bijective_of_nat_card_le hOeq
  obtain ⟨P, hP⟩ := hιbij.2 ⟨Q, hQ⟩
  obtain ⟨γ, hγ⟩ := P.2
  refine ⟨γ, ?_⟩
  have : (ι P).1 = Q := congrArg Subtype.val hP
  rw [← this]
  exact hγ.symm

end ModularCurve.Ws35FIXA

end KorbBlock

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve"
namespace Ws35FIXA

theorem forall_smul_eq_of_smul_generators_eq (q : ℕ) [NeZero q] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {G : Type*} [Group G] [MulSemiringAction G ↥(lambdaFieldOver q K)]
    (hGK : ∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → g • x = x)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (g : G) (hμ : g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) = σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K))) (hμq : g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) = σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K))) :
    ∀ x : ↥(lambdaFieldOver q K), g • x = σ x := by
  rintro ⟨x, hx⟩

  induction hx using Subfield.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · rw [hGK g _ hz, hσK _ hz]
    · rcases hz with rfl | hz
      · exact hμ
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hμq
  | one => rw [show (⟨1, _⟩ : ↥(lambdaFieldOver q K)) = 1 from rfl, smul_one, map_one]
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, _⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, smul_add, map_add, ihx, ihy]
  | neg x hx ih =>
    rw [show (⟨-x, _⟩ : ↥(lambdaFieldOver q K)) = -⟨x, hx⟩ from rfl, smul_neg, map_neg, ih]
  | inv x hx ih =>
    rw [show (⟨x⁻¹, _⟩ : ↥(lambdaFieldOver q K)) = (⟨x, hx⟩ : ↥(lambdaFieldOver q K))⁻¹ from rfl, smul_inv'', map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, _⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, MulSemiringAction.smul_mul, map_mul,
      ihx, ihy]

theorem exists_forall_smul_eq (q : ℕ) [NeZero q] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (a l : k) (h01728 : a = 0 ∨ a = 1728)
    {G : Type*} [Group G] [MulSemiringAction G ↥(lambdaFieldOver q K)]
    (hGK : ∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → g • x = x)
    (hGsurj : ∀ T Tq : LaurentSeries (AlgebraicClosure ℚ),
        ((T = lambdaModC (AlgebraicClosure ℚ) ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (T = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ Tq = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (T = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (T = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (T = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (T = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) →
        ∃ g : G, ((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = T ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = Tq)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ0 : a = 0 →
        ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
         (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))
    (hσ1728 : a = 1728 →
        ((16 * l = -1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (32 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (8 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹))) :
    ∃ g : G, ∀ x : ↥(lambdaFieldOver q K), g • x = σ x := by

  have hpair : ∃ T Tq : LaurentSeries (AlgebraicClosure ℚ),
      ((T = lambdaModC (AlgebraicClosure ℚ) ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (T = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ Tq = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (T = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (T = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (T = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (T = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) ∧
      (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = T ∧ (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = Tq := by
    rcases h01728 with rfl | rfl
    · obtain ⟨h1, h2⟩ := hσ0 rfl
      exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), h1, h2⟩
    · rcases hσ1728 rfl with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
      · exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h1, h2⟩
      · exact ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl⟩), h1, h2⟩
      · exact ⟨_, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))), h1, h2⟩
  obtain ⟨T, Tq, hcase, hσ1, hσ2⟩ := hpair
  obtain ⟨g, hg1, hg2⟩ := hGsurj T Tq hcase
  refine ⟨g, forall_smul_eq_of_smul_generators_eq q K hGK σ hσK g ?_ ?_⟩
  · exact Subtype.ext (hg1.trans hσ1.symm)
  · exact Subtype.ext (hg2.trans hσ2.symm)

end Ws35FIXA
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve"
namespace Ws35FIXA

theorem ringEquiv_apply_algebraMap_eq_of_forall_apply_algebraMap_algebraMap_eq
    {B S : Type*} [CommRing B] [CommRing S] [Algebra B S] (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime S P]
    (I : Ideal S)
    (e₁ e₂ : AdicCompletion I S ≃+* AdicCompletion I S)
    (h : ∀ b : B, e₁ (algebraMap S (AdicCompletion I S) (algebraMap B S b))
      = e₂ (algebraMap S (AdicCompletion I S) (algebraMap B S b)))
    (s : S) : e₁ (algebraMap S (AdicCompletion I S) s) = e₂ (algebraMap S (AdicCompletion I S) s) := by
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj P.primeCompl s

  simp only at hbc
  have hcu : IsUnit (algebraMap B S (c : B)) := IsLocalization.map_units S c
  have hu : IsUnit (e₂ (algebraMap S (AdicCompletion I S) (algebraMap B S (c : B)))) :=
    (hcu.map (algebraMap S (AdicCompletion I S))).map e₂
  have key : e₁ (algebraMap S (AdicCompletion I S) s) * e₂ (algebraMap S _ (algebraMap B S (c : B)))
      = e₂ (algebraMap S (AdicCompletion I S) s) * e₂ (algebraMap S _ (algebraMap B S (c : B))) := by
    have h1 : e₁ (algebraMap S (AdicCompletion I S) s) * e₁ (algebraMap S _ (algebraMap B S (c : B)))
        = e₁ (algebraMap S _ (algebraMap B S b)) := by
      rw [← map_mul, ← map_mul, hbc]
    have h2 : e₂ (algebraMap S (AdicCompletion I S) s) * e₂ (algebraMap S _ (algebraMap B S (c : B)))
        = e₂ (algebraMap S _ (algebraMap B S b)) := by
      rw [← map_mul, ← map_mul, hbc]
    rw [← h c, h1, h b, ← h2, h c]
  exact hu.mul_left_injective key

end Ws35FIXA
end ModularCurve

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
p2m_open "ModularCurve"
namespace Ws35FIXA

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

open scoped Pointwise

section EBHelpers
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
variable (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb)

abbrev SL (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (l : k)
    (K : IntermediateField ℚ Qb) : Subring LQ :=
  lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)

abbrev lev (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb) :
    MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* LQ :=
  lambdaEval q (coeffSubring A K)

abbrev pev (q : ℕ) {A : ValuationSubring Qb} {k : Type*} [Field k] (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb) :
    MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* k :=
  pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q)

theorem lev_ne_zero (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hp : pev q red l K p ≠ 0) : lev q A K p ≠ 0 := fun h =>
  hp (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K p h)

def HasVal (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (l : k)
    (K : IntermediateField ℚ Qb) (f : LQ) (v : k) : Prop :=
  ∃ r s : MvPolynomial (Fin 2) ↥(coeffSubring A K), pev q red l K s ≠ 0 ∧ f * lev q A K s = lev q A K r ∧ v * pev q red l K s = pev q red l K r

theorem mem_SL_of_hasVal {f : LQ} {v : k} (h : HasVal q A red l K f v) : f ∈ SL q A red l K := by
  obtain ⟨r, s, hs, hf, -⟩ := h
  exact ⟨r, s, hs, hf⟩

theorem exists_hasVal_of_mem {f : LQ} (hf : f ∈ SL q A red l K) : ∃ v, HasVal q A red l K f v := by
  obtain ⟨r, s, hs, hf⟩ := hf
  exact ⟨pev q red l K r / pev q red l K s, r, s, hs, hf, div_mul_cancel₀ _ hs⟩

theorem hasVal_lev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : HasVal q A red l K (lev q A K p) (pev q red l K p) :=
  ⟨p, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one], by rw [map_one, mul_one]⟩

theorem hasVal_unique (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ} {v v' : k}
    (h : HasVal q A red l K f v) (h' : HasVal q A red l K f v') : v = v' := by
  obtain ⟨r, s, hs, hf, hv⟩ := h
  obtain ⟨r', s', hs', hf', hv'⟩ := h'

  have hrel : lev q A K (r * s' - r' * s) = 0 := by
    simp only [map_sub, map_mul]
    rw [← hf, ← hf']; ring
  have hk := ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K _ hrel
  simp only [map_sub, map_mul] at hk

  have : v * (pev q red l K s * pev q red l K s') = v' * (pev q red l K s * pev q red l K s') := by
    calc v * (pev q red l K s * pev q red l K s') = (v * pev q red l K s) * pev q red l K s' := by ring
      _ = pev q red l K r * pev q red l K s' := by rw [hv]
      _ = pev q red l K r' * pev q red l K s := sub_eq_zero.mp hk
      _ = (v' * pev q red l K s') * pev q red l K s := by rw [hv']
      _ = v' * (pev q red l K s * pev q red l K s') := by ring
  exact mul_right_cancel₀ (mul_ne_zero hs hs') this

theorem hasVal_add {f g : LQ} {v w : k} (hf : HasVal q A red l K f v) (hg : HasVal q A red l K g w) :
    HasVal q A red l K (f + g) (v + w) := by
  obtain ⟨r, s, hs, hfs, hv⟩ := hf
  obtain ⟨r', s', hs', hgs, hw⟩ := hg
  refine ⟨r * s' + r' * s, s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_, ?_⟩
  · rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (lev q A K s * lev q A K s') = (f * lev q A K s) * lev q A K s' + (g * lev q A K s') * lev q A K s := by ring
      _ = _ := by rw [hfs, hgs]
  · rw [map_mul, map_add, map_mul, map_mul]
    calc (v + w) * (pev q red l K s * pev q red l K s') = (v * pev q red l K s) * pev q red l K s' + (w * pev q red l K s') * pev q red l K s := by ring
      _ = _ := by rw [hv, hw]

theorem hasVal_mul {f g : LQ} {v w : k} (hf : HasVal q A red l K f v) (hg : HasVal q A red l K g w) :
    HasVal q A red l K (f * g) (v * w) := by
  obtain ⟨r, s, hs, hfs, hv⟩ := hf
  obtain ⟨r', s', hs', hgs, hw⟩ := hg
  refine ⟨r * r', s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_, ?_⟩
  · rw [map_mul, map_mul]
    calc f * g * (lev q A K s * lev q A K s') = (f * lev q A K s) * (g * lev q A K s') := by ring
      _ = _ := by rw [hfs, hgs]
  · rw [map_mul, map_mul]
    calc v * w * (pev q red l K s * pev q red l K s') = (v * pev q red l K s) * (w * pev q red l K s') := by ring
      _ = _ := by rw [hv, hw]

theorem hasVal_inv (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ} {v : k} (hf : HasVal q A red l K f v) (hv : v ≠ 0) :
    HasVal q A red l K f⁻¹ v⁻¹ := by
  obtain ⟨r, s, hs, hfs, hvs⟩ := hf
  have hr : pev q red l K r ≠ 0 := by rw [← hvs]; exact mul_ne_zero hv hs
  have hr0 : lev q A K r ≠ 0 := lev_ne_zero red l K hq2 hl2 r hr
  have hf0 : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at hfs; exact hr0 hfs.symm
  refine ⟨s, r, hr, ?_, ?_⟩
  · rw [← hfs, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
  · rw [← hvs, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

theorem inv_mem_SL_of_hasVal (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ} {v : k}
    (hf : HasVal q A red l K f v) (hv : v ≠ 0) : f⁻¹ ∈ SL q A red l K :=
  mem_SL_of_hasVal red l K (hasVal_inv red l K hq2 hl2 hf hv)

theorem ne_zero_of_hasVal (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ} {v : k}
    (hf : HasVal q A red l K f v) (hv : v ≠ 0) : f ≠ 0 := by
  obtain ⟨r, s, hs, hfs, hvs⟩ := hf
  have hr : pev q red l K r ≠ 0 := by rw [← hvs]; exact mul_ne_zero hv hs
  rintro rfl; rw [zero_mul] at hfs; exact lev_ne_zero red l K hq2 hl2 r hr hfs.symm

theorem isUnit_of_hasVal (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ} {v : k}
    (hf : HasVal q A red l K f v) (hv : v ≠ 0) (hfm : f ∈ SL q A red l K) :
    IsUnit (⟨f, hfm⟩ : ↥(SL q A red l K)) := by
  have hf0 : f ≠ 0 := by
    obtain ⟨r, s, hs, hfs, hvs⟩ := hf
    have hr : pev q red l K r ≠ 0 := by rw [← hvs]; exact mul_ne_zero hv hs
    rintro rfl; rw [zero_mul] at hfs; exact lev_ne_zero red l K hq2 hl2 r hr hfs.symm
  refine isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, inv_mem_SL_of_hasVal red l K hq2 hl2 hf hv⟩, ?_⟩
  exact Subtype.ext (mul_inv_cancel₀ hf0)

theorem not_isUnit_of_hasVal_zero (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) {f : LQ}
    (hf : HasVal q A red l K f 0) (hfm : f ∈ SL q A red l K) :
    ¬ IsUnit (⟨f, hfm⟩ : ↥(SL q A red l K)) := by
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  obtain ⟨w, hw⟩ := exists_hasVal_of_mem red l K g.2
  have h1 : HasVal q A red l K (f * (g : LQ)) (0 * w) := hasVal_mul red l K hf hw
  rw [zero_mul] at h1
  have h1' : HasVal q A red l K (1 : LQ) (1 : k) := by
    have := hasVal_lev red l K (q := q) (A := A) (1 : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    rwa [map_one, map_one] at this
  have hfg : f * (g : LQ) = 1 := congrArg (fun z : ↥(SL q A red l K) => (z : LQ)) hg
  rw [hfg] at h1
  exact one_ne_zero (hasVal_unique red l K hq2 hl2 h1' h1)

theorem mem_maximalIdeal_iff_hasVal_zero (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l)
    [IsLocalRing ↥(SL q A red l K)] (f : ↥(SL q A red l K)) :
    f ∈ IsLocalRing.maximalIdeal ↥(SL q A red l K) ↔ HasVal q A red l K (f : LQ) 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    obtain ⟨v, hv⟩ := exists_hasVal_of_mem red l K f.2
    by_cases hv0 : v = 0
    · rwa [hv0] at hv
    · exact absurd (isUnit_of_hasVal red l K hq2 hl2 hv hv0 f.2) hnu
  · intro h0
    exact not_isUnit_of_hasVal_zero red l K hq2 hl2 h0 f.2

end EBHelpers

section StabBound
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem hasVal_ofNat (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb) (n : ℕ) [n.AtLeastTwo] :
    HasVal q A red l K (OfNat.ofNat n : LQ) (OfNat.ofNat n : k) := by
  have := hasVal_lev red l K (OfNat.ofNat n : MvPolynomial (Fin 2) ↥(coeffSubring A K))
  simpa only [map_ofNat] using this

theorem hasVal_one (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb) : HasVal q A red l K (1 : LQ) (1 : k) := by
  simpa only [map_one] using hasVal_lev red l K (1 : MvPolynomial (Fin 2) ↥(coeffSubring A K))

theorem hasVal_mu (red : A →+* k) (l : k) (K : IntermediateField ℚ Qb) : HasVal q A red l K (lambdaModC (AlgebraicClosure ℚ)) l := by
  have := hasVal_lev red l K (MvPolynomial.X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K))
  simpa [lambdaEval, pointEval] using this

theorem hasVal_sub {red : A →+* k} {l : k} {K : IntermediateField ℚ Qb} {f g : LQ} {v w : k}
    (hf : HasVal q A red l K f v) (hg : HasVal q A red l K g w) : HasVal q A red l K (f - g) (v - w) := by
  have hneg : HasVal q A red l K (-1 : LQ) (-1 : k) := by
    simpa only [map_neg, map_one] using hasVal_lev red l K (-1 : MvPolynomial (Fin 2) ↥(coeffSubring A K))
  have := hasVal_add red l K hf (hasVal_mul red l K hneg hg)
  simpa [sub_eq_add_neg] using this

theorem three_ne_zero_of_five_le (hq : 5 ≤ q) : (3 : k) ≠ 0 := by
  intro h
  have h3 : (3 : ℕ) = 0 ∨ q ∣ 3 := by
    have := (CharP.cast_eq_zero_iff k q 3).mp (by exact_mod_cast h)
    exact Or.inr this
  rcases h3 with h3 | h3
  · exact absurd h3 (by norm_num)
  · have := Nat.le_of_dvd (by norm_num) h3; omega

theorem two_ne_zero_of_five_le (hq : 5 ≤ q) : (2 : k) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff k q 2).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this; omega

theorem smul_pair_mem_of_mem_stabilizer (hq : 5 ≤ q) (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (K : IntermediateField ℚ Qb)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (B : Subring LQ) (hBS : B ≤ SL q A red l K) [IsLocalRing ↥(SL q A red l K)]
    (hμB : lambdaModC (AlgebraicClosure ℚ) ∈ B) (hμqB : lambdaNModC (AlgebraicClosure ℚ) q ∈ B)
    (hyB : CharPReduction.constSeries (coeffSubring A K) y ∈ B)
    {G : Type*} [Group G] [MulSemiringAction G ↥B]
    (hval : ∀ h : G, ((((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)))
    (hinj : ∀ h h' : G, ((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = ((h' • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) → ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = ((h' • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) → h = h')
    (hyfix : ∀ h : G, h • (⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B) = ⟨_, hyB⟩)
    (hμy : (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ - ⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B)
      ∈ (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)) :
    ∀ h : MulAction.stabilizer G ((IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)),
      ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q) ∨
      (a = 0 ∧ (((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))) ∨
      (a = 1728 ∧ ((16 * l + 1 = 0 ∧ ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) ∨ (32 * l - 1 = 0 ∧ ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q)) ∨
        (8 * l - 1 = 0 ∧ ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹)))) := by
  have hq2 : q ≠ 2 := by omega
  have hl2 : l ^ (q ^ 2) = l := pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l hla
  have h3 : (3 : k) ≠ 0 := three_ne_zero_of_five_le hq
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_five_le hq
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have h256 : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  set 𝔓 : Ideal ↥B := (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS) with h𝔓

  have hyv : HasVal q A red l K (CharPReduction.constSeries (coeffSubring A K) y) l := by
    have := hasVal_lev red l K (MvPolynomial.C y : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    simpa only [lambdaEval, pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, hy] using this
  have hμv := hasVal_mu red l K

  have hfix : ∀ h : MulAction.stabilizer G 𝔓, ∀ t : k,
      HasVal q A red l K ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ)) t → t = l := by
    intro h t ht
    have hmem : (h : G) • ((⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) - ⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩) ∈ 𝔓 :=
      AdicCompletion.smul_mem_of_mem_stabilizer (↥B) G 𝔓 h hμy
    rw [smul_sub, hyfix] at hmem
    have h0 := (mem_maximalIdeal_iff_hasVal_zero red l K hq2 hl2 _).mp (Ideal.mem_comap.mp hmem)
    have h1 : HasVal q A red l K ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) - CharPReduction.constSeries (coeffSubring A K) y) (t - l) :=
      hasVal_sub ht hyv
    exact sub_eq_zero.mp (hasVal_unique red l K hq2 hl2 h1 h0)

  have hroot0 : a = 0 → 256 * l ^ 2 - 16 * l + 1 = 0 := by
    rintro rfl
    have : ((16 * l) ^ 2 - 16 * l + 1) ^ 3 = 0 := by
      have h := hla; rw [zero_mul] at h
      rcases mul_eq_zero.mp h.symm with h | h
      · exact absurd h h256
      · exact h
    have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    linear_combination this
  have hroot1728 : a = 1728 → (16 * l + 1 = 0 ∨ 32 * l - 1 = 0 ∨ 8 * l - 1 = 0) := by
    rintro rfl

    have h64 : (64 : k) ≠ 0 := by
      have : (64 : k) = 2 ^ 6 := by norm_num
      rw [this]; exact pow_ne_zero _ h2
    have key64 : 64 * ((16 * l + 1) * (16 * l - 2) * (32 * l - 1)) ^ 2 = 0 := by
      linear_combination (-1 : k) * hla
    have key : ((16 * l + 1) * (16 * l - 2) * (32 * l - 1)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp key64 with h | h
      · exact absurd h h64
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · right; right
        have : 8 * l - 1 = (16 * l - 2) / 2 := by field_simp; ring
        rw [this, h, zero_div]
    · exact Or.inr (Or.inl h)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rcases h01728 with h | h
    · have := hroot0 h; norm_num at this
    · rcases hroot1728 h with h' | h' | h' <;> norm_num at h'
  have hl1 : 16 * l - 1 ≠ 0 := by
    intro e
    rcases h01728 with h | h
    · have r := hroot0 h
      exact one_ne_zero (by linear_combination r - (16 * l) * e : (1 : k) = 0)
    · rcases hroot1728 h with r | r | r
      · exact h2 (by linear_combination r - e : (2 : k) = 0)
      · exact one_ne_zero (by linear_combination r - (2 : k) * e : (1 : k) = 0)
      · exact one_ne_zero (by linear_combination e - (2 : k) * r : (1 : k) = 0)
  have hl16 : 16 - 256 * l ≠ 0 := by
    intro e
    have : (16 : k) * (16 * l - 1) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp this with h | h
    · exact h16 h
    · exact hl1 h

  have v16 : HasVal q A red l K (16 : LQ) (16 : k) := hasVal_ofNat red l K 16
  have v256 : HasVal q A red l K (256 : LQ) (256 : k) := hasVal_ofNat red l K 256
  have v1 : HasVal q A red l K (1 : LQ) (1 : k) := hasVal_one red l K
  have vT2 : HasVal q A red l K (16⁻¹ - lambdaModC (AlgebraicClosure ℚ)) (16⁻¹ - l) := hasVal_sub (hasVal_inv red l K hq2 hl2 v16 h16) hμv
  have vT3 : HasVal q A red l K ((256 * lambdaModC (AlgebraicClosure ℚ))⁻¹) ((256 * l)⁻¹) :=
    hasVal_inv red l K hq2 hl2 (hasVal_mul red l K v256 hμv) (mul_ne_zero h256 hl0)
  have vT4 : HasVal q A red l K ((16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹) ((16 - 256 * l)⁻¹) :=
    hasVal_inv red l K hq2 hl2 (hasVal_sub v16 (hasVal_mul red l K v256 hμv)) hl16
  have vT5 : HasVal q A red l K (lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹) (l * (16 * l - 1)⁻¹) :=
    hasVal_mul red l K hμv (hasVal_inv red l K hq2 hl2 (hasVal_sub (hasVal_mul red l K v16 hμv) v1) hl1)
  have vT6 : HasVal q A red l K ((16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹) ((16 * l - 1) * (256 * l)⁻¹) :=
    hasVal_mul red l K (hasVal_sub (hasVal_mul red l K v16 hμv) v1)
      (hasVal_inv red l K hq2 hl2 (hasVal_mul red l K v256 hμv) (mul_ne_zero h256 hl0))

  have eT2 : 16⁻¹ - l = l → 32 * l - 1 = 0 := fun e => by
    have e' := congrArg (fun t => 16 * t) e
    simp only [mul_sub, mul_inv_cancel₀ h16] at e'
    linear_combination -e'
  have eT3 : (256 * l)⁻¹ = l → 256 * l ^ 2 - 1 = 0 := fun e => by
    have e' := congrArg (fun t => 256 * l * t) e
    simp only [mul_inv_cancel₀ (mul_ne_zero h256 hl0)] at e'
    linear_combination -e'
  have eT4 : (16 - 256 * l)⁻¹ = l → 256 * l ^ 2 - 16 * l + 1 = 0 := fun e => by
    have e' := congrArg (fun t => (16 - 256 * l) * t) e
    simp only [mul_inv_cancel₀ hl16] at e'
    linear_combination e'
  have eT5 : l * (16 * l - 1)⁻¹ = l → 8 * l - 1 = 0 := fun e => by
    have e' := congrArg (fun t => t * (16 * l - 1)) e
    simp only [inv_mul_cancel_right₀ hl1] at e'

    have : l * (16 * l - 2) = 0 := by linear_combination -e'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hl0
    · have : (2 : k) * (8 * l - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' h2
      · exact h'
  have eT6 : (16 * l - 1) * (256 * l)⁻¹ = l → 256 * l ^ 2 - 16 * l + 1 = 0 := fun e => by
    have e' := congrArg (fun t => t * (256 * l)) e
    simp only [inv_mul_cancel_right₀ (mul_ne_zero h256 hl0)] at e'
    linear_combination -e'

  intro h
  have hfx := hfix h
  rcases hval (h : G) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩

  · exact Or.inl ⟨e1, e2⟩

  · have c := eT2 (hfx _ (by rw [e1]; exact vT2))
    rcases h01728 with h0 | h0
    · exfalso; have r := hroot0 h0
      exact h3 (by linear_combination (4 : k) * r - (32 * l - 1) * c)
    · right; right
      refine ⟨h0, Or.inr (Or.inl ⟨c, e1, e2⟩)⟩

  · have c := eT3 (hfx _ (by rw [e1]; exact vT3))
    rcases h01728 with h0 | h0
    · exfalso; have r := hroot0 h0
      exact h3 (by linear_combination (16 * l + 2) * r - (16 * l + 1) * c)
    · rcases hroot1728 h0 with c3 | c3 | c3
      · right; right
        exact ⟨h0, Or.inl ⟨c3, e1, e2⟩⟩
      · exfalso; exact h3 (by linear_combination (32 * l + 1) * c3 - (4 : k) * c)
      · exfalso; exact h3 (by linear_combination c - (32 * l + 4) * c3)

  · have c := eT4 (hfx _ (by rw [e1]; exact vT4))
    rcases h01728 with h0 | h0
    · right; left
      exact ⟨h0, Or.inl ⟨e1, e2⟩⟩
    · exfalso
      rcases hroot1728 h0 with c3 | c3 | c3
      · exact h3 (by linear_combination c - (16 * l - 2) * c3)
      · exact h3 (by linear_combination (4 : k) * c - (32 * l - 1) * c3)
      · exact h3 (by linear_combination c - (32 * l + 2) * c3)

  · have c := eT5 (hfx _ (by rw [e1]; exact vT5))
    rcases h01728 with h0 | h0
    · exfalso; have r := hroot0 h0
      exact h3 (by linear_combination r - (32 * l + 2) * c)
    · rcases hroot1728 h0 with c3 | c3 | c3
      · exfalso; exact h3 (by linear_combination c3 - (2 : k) * c)
      · exfalso; exact h3 (by linear_combination c3 - (4 : k) * c)
      · right; right
        exact ⟨h0, Or.inr (Or.inr ⟨c3, e1, e2⟩)⟩

  · have c := eT6 (hfx _ (by rw [e1]; exact vT6))
    rcases h01728 with h0 | h0
    · right; left
      exact ⟨h0, Or.inr ⟨e1, e2⟩⟩
    · exfalso
      rcases hroot1728 h0 with c3 | c3 | c3
      · exact h3 (by linear_combination c - (16 * l - 2) * c3)
      · exact h3 (by linear_combination (4 : k) * c - (32 * l - 1) * c3)
      · exact h3 (by linear_combination c - (32 * l + 2) * c3)

theorem card_stabilizer_le (hq : 5 ≤ q) (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (K : IntermediateField ℚ Qb)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (B : Subring LQ) (hBS : B ≤ SL q A red l K) [IsLocalRing ↥(SL q A red l K)]
    (hμB : lambdaModC (AlgebraicClosure ℚ) ∈ B) (hμqB : lambdaNModC (AlgebraicClosure ℚ) q ∈ B)
    (hyB : CharPReduction.constSeries (coeffSubring A K) y ∈ B)
    {G : Type*} [Group G] [MulSemiringAction G ↥B]
    (hval : ∀ h : G, ((((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)))
    (hinj : ∀ h h' : G, ((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) = ((h' • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ) → ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) = ((h' • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ) → h = h')
    (hyfix : ∀ h : G, h • (⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B) = ⟨_, hyB⟩)
    (hμy : (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ - ⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B)
      ∈ (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)) :
    Nat.card (MulAction.stabilizer G ((IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)))
      ≤ jWidth a := by
  classical
  have hq2 : q ≠ 2 := by omega
  have h3 : (3 : k) ≠ 0 := three_ne_zero_of_five_le hq
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_five_le hq
  have hmem := smul_pair_mem_of_mem_stabilizer hq red a h01728 K l hla y hy B hBS hμB hμqB hyB hval hinj hyfix hμy
  set 𝔓 : Ideal ↥B := (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS) with h𝔓
  set P := (if a = 0 then ({(lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) q), ((16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹, (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹), ((16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹, (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)} : Finset ((LaurentSeries (AlgebraicClosure ℚ)) × (LaurentSeries (AlgebraicClosure ℚ))))
        else if 16 * l + 1 = 0 then {(lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) q), ((256 * lambdaModC (AlgebraicClosure ℚ))⁻¹, (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)}
        else if 32 * l - 1 = 0 then {(lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) q), (16⁻¹ - lambdaModC (AlgebraicClosure ℚ), 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q)}
        else {(lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) q), (lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹, lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹)}) with hP
  have h1728 : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hPcard : P.card ≤ jWidth a := by
    rcases h01728 with rfl | rfl
    · rw [jWidth_of_eq_zero rfl, hP, if_pos rfl]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ (Finset.card_singleton _).le)))
    · rw [jWidth_of_eq_1728 rfl h1728, hP, if_neg h1728]
      split_ifs <;>
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_singleton _).le)
  have hmemP : ∀ h : MulAction.stabilizer G 𝔓,
      ((((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LQ), (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LQ)) ∈ P := by
    intro h
    rw [hP]
    rcases hmem h with ⟨e1, e2⟩ | ⟨h0, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ | ⟨h0, ⟨c, e1, e2⟩ | ⟨c, e1, e2⟩ | ⟨c, e1, e2⟩⟩
    · rw [e1, e2]; split_ifs <;> simp
    · rw [e1, e2, if_pos h0]; simp
    · rw [e1, e2, if_pos h0]; simp
    · rw [e1, e2, if_neg (h0 ▸ h1728), if_pos c]; simp
    · have c1 : ¬ (16 * l + 1 = 0) := fun e => h3 (by linear_combination (2 : k) * e - c)
      rw [e1, e2, if_neg (h0 ▸ h1728), if_neg c1, if_pos c]; simp
    · have c1 : ¬ (16 * l + 1 = 0) := fun e => h3 (by linear_combination e - (2 : k) * c)
      have c2 : ¬ (32 * l - 1 = 0) := fun e => h3 (by linear_combination e - (4 : k) * c)
      rw [e1, e2, if_neg (h0 ▸ h1728), if_neg c1, if_neg c2]; simp
  let f : MulAction.stabilizer G 𝔓 → ↥P := fun h => ⟨_, hmemP h⟩
  have hf : Function.Injective f := by
    intro h h' e
    have e' := congrArg Subtype.val e
    simp only [f, Prod.mk.injEq] at e'
    exact Subtype.ext (hinj _ _ e'.1 e'.2)
  calc Nat.card (MulAction.stabilizer G 𝔓) ≤ Nat.card ↥P := Nat.card_le_card_of_injective f hf
    _ = P.card := Nat.card_eq_finsetCard P
    _ ≤ jWidth a := hPcard

end StabBound

end Ws35FIXA
end ModularCurve
end

section PairBlock
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"
namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero"
namespace Ws35FIXA
p2m_open "ModularCurve"

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

scoped instance charZero_laurentSeries_algClosure' : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

theorem lambdaModC_ne_zero : lambdaModC Qb ≠ 0 := by
  intro h
  have hinj := transcendental_iff_injective.mp (ModularCurve.transcendental_lambdaModC Qb)
  have : (Polynomial.X : Polynomial Qb) = 0 := hinj (by rw [Polynomial.aeval_X, h, map_zero])
  exact Polynomial.X_ne_zero this

theorem sixteen_sub_ne_zero : (16 : LQ) - 256 * lambdaModC Qb ≠ 0 := by
  intro h
  have hinj := transcendental_iff_injective.mp (ModularCurve.transcendental_lambdaModC Qb)
  have : (Polynomial.C 16 - Polynomial.C 256 * Polynomial.X : Polynomial Qb) = 0 := hinj (by
    rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, map_zero,
      map_ofNat, map_ofNat]
    exact h)
  have h1 := congrArg (Polynomial.coeff · 1) this
  simp at h1

theorem lambdaNModC_ne_zero (q : ℕ) [NeZero q] : lambdaNModC Qb q ≠ 0 := by
  rw [lambdaNModC]
  intro h
  exact lambdaModC_ne_zero ((qExpand Qb q).injective (by rw [h, map_zero]))

theorem sixteen_sub_N_ne_zero (q : ℕ) [NeZero q] : (16 : LQ) - 256 * lambdaNModC Qb q ≠ 0 := by
  rw [lambdaNModC]
  intro h
  apply sixteen_sub_ne_zero
  apply (qExpand Qb q).injective
  rw [map_sub, map_mul, map_ofNat, map_ofNat, h, map_zero]

theorem subst4_sq_formula (t : LQ) (ht : t ≠ 0) (h16 : (16 : LQ) - 256 * t ≠ 0) :
    ((16 : LQ) - 256 * (16 - 256 * t)⁻¹)⁻¹ = (16 * t - 1) * (256 * t)⁻¹ := by
  have h256 : (256 : LQ) ≠ 0 := by norm_num
  have hden : (16 : LQ) - 256 * (16 - 256 * t)⁻¹ ≠ 0 := by
    intro h0
    have : ((16 : LQ) - 256 * (16 - 256 * t)⁻¹) * (16 - 256 * t) = 0 := by rw [h0, zero_mul]
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ h16, mul_one] at this
    have ht' : (4096 : LQ) * t = 0 := by linear_combination -this
    exact ht ((mul_eq_zero.mp ht').resolve_left (by norm_num))
  have h16' : (16 : LQ) - t * 256 ≠ 0 := by rwa [mul_comm] at h16
  have h4096 : (4096 : LQ) ≠ 0 := by norm_num
  symm
  apply eq_inv_of_mul_eq_one_left

  have hu : (16 - 256 * t)⁻¹ * (16 - 256 * t) = 1 := inv_mul_cancel₀ h16
  have hv : (256 * t)⁻¹ * (256 * t) = 1 := inv_mul_cancel₀ (mul_ne_zero h256 ht)
  linear_combination (16 * (256 * t)⁻¹) * hu + hv

theorem smul_smul_generators_of_smul_eq_subst4 (q : ℕ) [NeZero q] (K : IntermediateField ℚ Qb)
    {G : Type*} [Group G] [MulSemiringAction G ↥(lambdaFieldOver q K)] (γ : G)
    (h1 : ((γ • (⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LQ)
        = (16 - 256 * lambdaModC Qb)⁻¹)
    (h2 : ((γ • (⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LQ)
        = (16 - 256 * lambdaNModC Qb q)⁻¹) :
    ((γ • (γ • (⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K))) : ↥(lambdaFieldOver q K)) : LQ)
        = (16 * lambdaModC Qb - 1) * (256 * lambdaModC Qb)⁻¹ ∧
    ((γ • (γ • (⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K))) : ↥(lambdaFieldOver q K)) : LQ)
        = (16 * lambdaNModC Qb q - 1) * (256 * lambdaNModC Qb q)⁻¹ := by
  have hsmul : ∀ x : ↥(lambdaFieldOver q K), γ • x = MulSemiringAction.toRingHom G ↥(lambdaFieldOver q K) γ x :=
    fun x => rfl

  have step : ∀ x : ↥(lambdaFieldOver q K), ((γ • x : ↥(lambdaFieldOver q K)) : LQ) = (16 - 256 * (x : LQ))⁻¹ →
      ((γ • (γ • x) : ↥(lambdaFieldOver q K)) : LQ) = (16 - 256 * (16 - 256 * (x : LQ))⁻¹)⁻¹ := by
    intro x hx
    have hxL : γ • x = (16 - 256 * x)⁻¹ := by
      apply Subtype.ext
      rw [hx]
      push_cast
      rfl
    rw [hxL, hsmul, map_inv₀, map_sub, map_mul, map_ofNat, map_ofNat, ← hsmul, hxL]
    push_cast
    rfl
  refine ⟨?_, ?_⟩
  · rw [step _ h1]
    exact subst4_sq_formula _ lambdaModC_ne_zero sixteen_sub_ne_zero
  · rw [step _ h2]
    exact subst4_sq_formula _ (lambdaNModC_ne_zero q) (sixteen_sub_N_ne_zero q)

end ModularCurve.Ws35FIXA
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve.Ws35FIXA"
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve"

end PairBlock
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve.Ws35FIXA"

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos LambdaNodeLocalized.exists_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_isMaximal LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero" namespace Ws35FIXA end ModularCurve.Ws35FIXA
p2m_open_scoped "ModularCurve" in
open Pointwise in
set_option maxHeartbeats 16000000 in

theorem ModularCurve.Ws35FIXA.mainFIXA
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ6 : ∀ x : ↥(lambdaFieldOver q K), σ^[6] x = x)
    (hσ0 : a = 0 →
        ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
         (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))
    (hσ1728 : a = 1728 →
        ((16 * l = -1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (32 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (8 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹)))
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))] [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    (hSF : (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ (lambdaFieldOver q K).toSubring)
    (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hg : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), ((g z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((σ ⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hSF z.2⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)))
    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hĝ : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), ĝ (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ z) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (g z)) :
    ∃ (A' : Subring (LaurentSeries (AlgebraicClosure ℚ)))
      (hRA : ∀ z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q), qExpand (AlgebraicClosure ℚ) 2 z ∈ A')
      (hAS : A' ≤ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
      (_ : IsLocalRing ↥A') (_ : IsNoetherianRing ↥A'),

      (letI : Algebra ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥A' :=
        (((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).codRestrict A'
          (fun z => hRA z z.2)).toAlgebra
       Module.Finite ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥A') ∧

      (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hAS) = IsLocalRing.maximalIdeal ↥A' ∧

      (∀ z : ↥A', ∃ o : ↥(coeffSubring A K),
        z - ⟨qExpand (AlgebraicClosure ℚ) 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o)),
              hRA _ (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _)⟩
          ∈ IsLocalRing.maximalIdeal ↥A') ∧

      ∃ eA : AdicCompletion (IsLocalRing.maximalIdeal ↥A') ↥A' ≃+*
          ↥((ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) →+* _).eqLocus (RingHom.id _)),
        ∀ z : ↥A', ((eA (algebraMap ↥A' _ z) : ↥((ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) →+* _).eqLocus (RingHom.id _))) :
            AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (Subring.inclusion hAS z) := by
  classical
  have hq2 : q ≠ 2 := by omega
  have hl2 : l ^ (q ^ 2) = l := pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l hla

  set R0 : Subring (LaurentSeries (AlgebraicClosure ℚ)) := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hR0
  let S : Subring (LaurentSeries (AlgebraicClosure ℚ)) := lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)
  let φ : LaurentSeries (AlgebraicClosure ℚ) →+* LaurentSeries (AlgebraicClosure ℚ) := qExpand (AlgebraicClosure ℚ) 2

  obtain ⟨B, hB⟩ : ∃ B : Subring (LaurentSeries (AlgebraicClosure ℚ)), ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ B ↔
      z ∈ lambdaFieldOver q K ∧ (φ.comp R0.subtype).IsIntegralElem z := by
    letI : Algebra ↥R0 (LaurentSeries (AlgebraicClosure ℚ)) := (φ.comp R0.subtype).toAlgebra
    refine ⟨{ carrier := {z | z ∈ lambdaFieldOver q K ∧ IsIntegral ↥R0 z}
              zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
              one_mem' := ⟨one_mem _, isIntegral_one⟩
              add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
              neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
              mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩ }, fun z => Iff.rfl⟩
  obtain ⟨hRB, hTB, hBS, h𝔓max, hloc, hmark⟩ :=
    ModularCurve.LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem hq red a ha ha2 h01728 K
      l hla y hy B hB

  obtain ⟨G, _instG, _instF, _instA, hcard, hfaith, hGK, hGF0, hGval, hGsurj⟩ :=
    ModularCurve.LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver q hq2 K
  have hBL : ∀ z ∈ B, z ∈ lambdaFieldOver q K := fun z hz => ((hB z).mp hz).1

  have hR0F0 : ∀ z ∈ R0, z ∈ fieldOver (1 * q) K := fun z hz =>
    ModularCurve.Ws35FIXA.R₀_le_fieldOver q A red a K hz

  have hRL : ∀ z : ↥R0, φ z ∈ lambdaFieldOver q K := fun z => hBL _ (hRB z z.2)
  let ψ : ↥R0 →+* ↥(lambdaFieldOver q K) := (φ.comp R0.subtype).codRestrict _ hRL
  have hψ : (lambdaFieldOver q K).subtype.comp ψ = φ.comp R0.subtype := RingHom.ext fun _ => rfl
  have hGψ : ∀ γ : G, (MulSemiringAction.toRingHom G ↥(lambdaFieldOver q K) γ).comp ψ = ψ := by
    intro γ
    refine RingHom.ext fun z => ?_
    exact hGF0 γ (ψ z) (Subfield.mem_map.mpr ⟨z, hR0F0 z z.2, rfl⟩)
  have hGB : ∀ (γ : G) (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : z ∈ B),
      ((γ • (⟨z, hBL z hz⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ B := by
    intro γ z hz
    obtain ⟨hzL, p, hpm, hpz⟩ := (hB z).mp hz
    refine (hB _).mpr ⟨Subtype.coe_prop _, p, hpm, ?_⟩

    set zL : ↥(lambdaFieldOver q K) := ⟨z, hBL z hz⟩
    have hpzL : Polynomial.eval₂ ψ zL p = 0 := by
      apply (lambdaFieldOver q K).subtype_injective
      rw [Polynomial.hom_eval₂ p ψ (lambdaFieldOver q K).subtype zL, hψ, map_zero]
      exact hpz
    have h2 : Polynomial.eval₂ ψ (γ • zL) p = 0 := by
      have := congrArg (MulSemiringAction.toRingHom G ↥(lambdaFieldOver q K) γ) hpzL
      rw [Polynomial.hom_eval₂ p ψ, hGψ γ, map_zero] at this
      exact this
    have := congrArg (lambdaFieldOver q K).subtype h2
    rw [Polynomial.hom_eval₂ p ψ (lambdaFieldOver q K).subtype, hψ, map_zero] at this
    exact this

  let toL : ↥B → ↥(lambdaFieldOver q K) := fun b => ⟨(b : LaurentSeries (AlgebraicClosure ℚ)), hBL _ b.2⟩
  have toL_zero : toL 0 = 0 := rfl
  have toL_one : toL 1 = 1 := rfl
  have toL_add : ∀ b c : ↥B, toL (b + c) = toL b + toL c := fun _ _ => rfl
  have toL_mul : ∀ b c : ↥B, toL (b * c) = toL b * toL c := fun _ _ => rfl
  letI actB : MulSemiringAction G ↥B :=
    { smul := fun γ b => ⟨((γ • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)), hGB γ _ b.2⟩
      one_smul := fun b => Subtype.ext (by
        show (((1 : G) • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = b
        rw [one_smul])
      mul_smul := fun γ δ b => Subtype.ext (by
        show (((γ * δ) • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • toL ⟨((δ • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)), hGB δ _ b.2⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [mul_smul])
      smul_zero := fun γ => Subtype.ext (by
        show ((γ • toL 0 : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 0
        rw [toL_zero, smul_zero]; rfl)
      smul_add := fun γ b c => Subtype.ext (by
        show ((γ • toL (b + c) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) + ((γ • toL c : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [toL_add, smul_add]; rfl)
      smul_one := fun γ => Subtype.ext (by
        show ((γ • toL 1 : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 1
        rw [toL_one, smul_one]; rfl)
      smul_mul := fun γ b c => Subtype.ext (by
        show ((γ • toL (b * c) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) * ((γ • toL c : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [toL_mul, MulSemiringAction.smul_mul]; rfl) }
  have smulB_coe : ∀ (γ : G) (b : ↥B), ((γ • b : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • toL b : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun _ _ => rfl

  let A' : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
    { carrier := {z | ∃ hz : z ∈ B, ∀ γ : G, γ • (⟨z, hz⟩ : ↥B) = ⟨z, hz⟩}
      zero_mem' := ⟨zero_mem _, fun γ => (smul_zero γ : (γ • (0 : ↥B)) = 0)⟩
      one_mem' := ⟨one_mem _, fun γ => (smul_one γ : (γ • (1 : ↥B)) = 1)⟩
      add_mem' := by
        rintro x y ⟨hx, hGx⟩ ⟨hy, hGy⟩
        refine ⟨add_mem hx hy, fun γ => ?_⟩
        have := congrArg₂ (· + ·) (hGx γ) (hGy γ)
        simpa [← smul_add] using this
      neg_mem' := by
        rintro x ⟨hx, hGx⟩
        refine ⟨neg_mem hx, fun γ => ?_⟩
        have := congrArg Neg.neg (hGx γ)
        simp [← smul_neg] at this
        exact this
      mul_mem' := by
        rintro x y ⟨hx, hGx⟩ ⟨hy, hGy⟩
        refine ⟨mul_mem hx hy, fun γ => ?_⟩
        have := congrArg₂ (· * ·) (hGx γ) (hGy γ)
        simpa [← MulSemiringAction.smul_mul] using this }
  have hA'B : A' ≤ B := fun z hz => hz.1
  have hAS : A' ≤ S := fun z hz => hBS (hA'B hz)

  have hRA : ∀ z ∈ R0, φ z ∈ A' := by
    intro z hz
    refine ⟨hRB z hz, fun γ => Subtype.ext ?_⟩
    rw [smulB_coe]
    exact congrArg Subtype.val (hGF0 γ (toL ⟨φ z, hRB z hz⟩) (Subfield.mem_map.mpr ⟨z, hR0F0 z hz, rfl⟩))

  letI algRB : Algebra ↥R0 ↥B := ((φ.comp R0.subtype).codRestrict B (fun z => hRB z z.2)).toAlgebra
  haveI finRB : Module.Finite ↥R0 ↥B :=
    ModularCurve.LambdaNodeLocalized.moduleFinite_of_forall_mem_iff_isIntegralElem_qExpand_modularLocalizedAtPoint
      red a K B hB hRB
  letI algAB : Algebra ↥A' ↥B := (Subring.inclusion hA'B).toAlgebra
  letI algRA : Algebra ↥R0 ↥A' := ((φ.comp R0.subtype).codRestrict A' (fun z => hRA z z.2)).toAlgebra
  haveI towerRAB : IsScalarTower ↥R0 ↥A' ↥B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherian ↥R0 ↥B := isNoetherian_of_isNoetherianRing_of_finite ↥R0 ↥B
  haveI finRA : Module.Finite ↥R0 ↥A' :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom ↥R0 ↥A' ↥B).toLinearMap (Subring.inclusion_injective hA'B)
  haveI noethA : IsNoetherianRing ↥A' := Algebra.FiniteType.isNoetherianRing ↥R0 ↥A'
  haveI finAB : Module.Finite ↥A' ↥B := Module.Finite.of_restrictScalars_finite ↥R0 ↥A' ↥B
  haveI faithAB : FaithfulSMul ↥A' ↥B :=
    (faithfulSMul_iff_algebraMap_injective ↥A' ↥B).mpr (Subring.inclusion_injective hA'B)
  haveI commGAB : SMulCommClass G ↥A' ↥B :=
    ⟨fun γ x b => by
      rw [Algebra.smul_def, Algebra.smul_def, MulSemiringAction.smul_mul]
      congr 1
      exact x.2.2 γ⟩
  haveI invAB : Algebra.IsInvariant ↥A' ↥B G :=
    ⟨fun b hb => ⟨⟨(b : LaurentSeries (AlgebraicClosure ℚ)), b.2, fun γ => by simpa using hb γ⟩, Subtype.ext rfl⟩⟩
  haveI : Finite G := Finite.of_fintype G

  letI algBS : Algebra ↥B ↥S := (Subring.inclusion hBS).toAlgebra
  set 𝔓 : Ideal ↥B := (IsLocalRing.maximalIdeal ↥S).comap (Subring.inclusion hBS) with h𝔓def
  haveI : 𝔓.IsMaximal := h𝔓max
  haveI : Algebra.IsIntegral ↥A' ↥B := Algebra.IsIntegral.of_finite ↥A' ↥B

  have hμB : lambdaModC (AlgebraicClosure ℚ) ∈ B := by
    simpa [lambdaEval] using hTB (MvPolynomial.X 0)
  have hμqB : lambdaNModC (AlgebraicClosure ℚ) q ∈ B := by
    simpa [lambdaEval] using hTB (MvPolynomial.X 1)
  have hyB : CharPReduction.constSeries (coeffSubring A K) y ∈ B := by
    simpa [lambdaEval] using hTB (MvPolynomial.C y)
  have hval : ∀ h : G, ((((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) := by
    intro h
    have := hGval h
    rw [smulB_coe, smulB_coe]
    exact this
  have hinjG : ∀ h h' : G, ((h • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((h' • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) → ((h • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((h' • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) → h = h' := by
    intro h h' e1 e2
    rw [smulB_coe, smulB_coe] at e1
    rw [smulB_coe, smulB_coe] at e2

    have key : ∀ x : ↥(lambdaFieldOver q K), (h'⁻¹ * h) • x = x := by
      have hh : ∀ x : ↥(lambdaFieldOver q K), h • x = (MulSemiringAction.toRingEquiv G ↥(lambdaFieldOver q K) h') x := by
        refine ModularCurve.Ws35FIXA.forall_smul_eq_of_smul_generators_eq q K hGK
          (MulSemiringAction.toRingEquiv G ↥(lambdaFieldOver q K) h') (fun x hx => hGK h' x hx) h ?_ ?_
        · exact Subtype.ext e1
        · exact Subtype.ext e2
      intro x
      rw [mul_smul, hh, MulSemiringAction.toRingEquiv_apply, inv_smul_smul]
    have := hfaith (h'⁻¹ * h) key
    exact (inv_mul_eq_one.mp this).symm
  have hyfix : ∀ h : G, h • (⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B) = ⟨_, hyB⟩ := by
    intro h
    apply Subtype.ext
    rw [smulB_coe]
    exact congrArg Subtype.val (hGK h (toL ⟨_, hyB⟩) ⟨⟨(y : AlgebraicClosure ℚ), y.2.2⟩, rfl⟩)
  have hμy : (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ - ⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ : ↥B) ∈ 𝔓 := by
    have hp : pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q)
        (MvPolynomial.X 0 - MvPolynomial.C y : MvPolynomial (Fin 2) ↥(coeffSubring A K)) = 0 := by
      simp [pointEval, hy]
    have hmem : lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y) ∈ B := hTB _
    have := hmark _ hp hmem
    have e : (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y), hmem⟩ : ↥B)
        = ⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ - ⟨CharPReduction.constSeries (coeffSubring A K) y, hyB⟩ :=
      Subtype.ext (by simp [lambdaEval])
    rw [← e]
    exact this
  have hstab : Nat.card (MulAction.stabilizer G 𝔓) ≤ jWidth a :=
    ModularCurve.Ws35FIXA.card_stabilizer_le hq red a h01728 K l hla y hy B hBS hμB hμqB hyB hval hinjG hyfix hμy
  have Korb : ∀ Q : Ideal ↥B, Q.IsMaximal → ∃ γ : G, Q = γ • 𝔓 := fun Q hQ =>
    ModularCurve.Ws35FIXA.exists_smul_eq_of_isMaximal hq red a ha ha2 h01728 K ϖ hϖ l hla y hy B hB hBS h𝔓max hcard hstab Q hQ
  have K1 : ∃ _ : IsLocalRing ↥A', IsLocalRing.maximalIdeal ↥A' = 𝔓.under ↥A' :=
    Algebra.IsInvariant.exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq 𝔓 Korb
  obtain ⟨locA, hmaxA⟩ := K1
  haveI := locA
  haveI : 𝔓.LiesOver (IsLocalRing.maximalIdeal ↥A') := ⟨hmaxA⟩

  letI := AdicCompletion.stabilizerMulSemiringAction ↥A' ↥B G 𝔓
  haveI := AdicCompletion.stabilizer_smulCommClass ↥A' ↥B G 𝔓
  let eInv := AdicCompletion.invariantsCompletionRingEquiv ↥A' ↥B G (IsLocalRing.maximalIdeal ↥A') 𝔓

  haveI : IsLocalization.AtPrime ↥S 𝔓 := hloc
  have K2 : ∃ T : AdicCompletion 𝔓 ↥B ≃+* AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S,
      ∀ b : ↥B, T (algebraMap ↥B (AdicCompletion 𝔓 ↥B) b)
        = algebraMap ↥S (AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S) (Subring.inclusion hBS b) :=
    AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal 𝔓
  obtain ⟨T, hT⟩ := K2

  obtain ⟨γ₀, hγ₀⟩ := ModularCurve.Ws35FIXA.exists_forall_smul_eq q K a l h01728 hGK hGsurj σ hσK hσ0 hσ1728
  have hγ₀B : ∀ b : ↥B, Subring.inclusion hBS (γ₀ • b) = g (Subring.inclusion hBS b) := by
    intro b
    apply Subtype.ext
    show ((γ₀ • b : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((g (Subring.inclusion hBS b) : ↥S) : LaurentSeries (AlgebraicClosure ℚ))
    rw [smulB_coe, hγ₀, hg]
    rfl

  have hγ₀stab : γ₀ ∈ MulAction.stabilizer G 𝔓 := by
    rw [MulAction.mem_stabilizer_iff]
    have hle : γ₀ • 𝔓 ≤ 𝔓 := by
      intro x hx
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have : x = γ₀ • (γ₀⁻¹ • x) := (smul_inv_smul γ₀ x).symm
      rw [this, h𝔓def, Ideal.mem_comap]
      show Subring.inclusion hBS (γ₀ • (γ₀⁻¹ • x)) ∈ IsLocalRing.maximalIdeal ↥S
      rw [hγ₀B]
      have hx' : Subring.inclusion hBS (γ₀⁻¹ • x) ∈ IsLocalRing.maximalIdeal ↥S := Ideal.mem_comap.mp hx
      rw [IsLocalRing.mem_maximalIdeal] at hx' ⊢
      intro hu
      exact hx' (by simpa using hu.map g.symm)
    have hmax' : (γ₀ • 𝔓).IsMaximal :=
      (AdicCompletion.smul_mem_index ↥A' ↥B G (IsLocalRing.maximalIdeal ↥A') γ₀
        ⟨h𝔓max, Ideal.map_le_iff_le_comap.mpr (le_of_eq hmaxA)⟩).1
    exact hmax'.eq_of_le h𝔓max.ne_top hle
  let s₀ : MulAction.stabilizer G 𝔓 := ⟨γ₀, hγ₀stab⟩

  have hK3id : ∀ z, T (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀ (T.symm z)) = ĝ z := by
    let e₁ : AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S ≃+* AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S :=
      (T.symm.trans (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀).toRingEquiv).trans T
    have he : e₁ = ĝ := by
      apply AdicCompletion.ringEquiv_eq_of_forall_apply_algebraMap_eq_of_isLocalRing
      intro s
      refine ModularCurve.Ws35FIXA.ringEquiv_apply_algebraMap_eq_of_forall_apply_algebraMap_algebraMap_eq 𝔓 _ e₁ ĝ ?_ s
      intro b
      show T (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀ (T.symm (algebraMap ↥S _ (algebraMap ↥B ↥S b)))) = ĝ (algebraMap ↥S _ (algebraMap ↥B ↥S b))
      have hb : algebraMap ↥B ↥S b = Subring.inclusion hBS b := rfl
      rw [hb, hĝ, ← hγ₀B, ← hT (γ₀ • b), ← hT b, RingEquiv.symm_apply_apply]
      congr 1
      try exact AdicCompletion.stabilizerToCompletionAut_of ↥A' ↥B G 𝔓 s₀ b
    intro z
    exact congrArg (fun e : AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S ≃+* _ => e z) he

  have hgen : ∀ h : MulAction.stabilizer G 𝔓, h = 1 ∨ h = s₀ ∨ h = s₀ ^ 2 := by
    have h3k : (3 : k) ≠ 0 := ModularCurve.Ws35FIXA.three_ne_zero_of_five_le hq
    have hvals := ModularCurve.Ws35FIXA.smul_pair_mem_of_mem_stabilizer hq red a h01728 K l hla y hy B hBS
      hμB hμqB hyB hval hinjG hyfix hμy

    have pμ : ((γ₀ • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [smulB_coe, hγ₀]
    have pμq : ((γ₀ • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [smulB_coe, hγ₀]
    have psq : ∀ b : ↥B, (((γ₀ ^ 2) • b : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ₀ • (γ₀ • toL b) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      intro b
      rw [pow_two, mul_smul, smulB_coe]
      have : toL (γ₀ • b) = γ₀ • toL b := Subtype.ext (smulB_coe γ₀ b)
      rw [this]

    have idG : ∀ (h : MulAction.stabilizer G 𝔓) (γ : G),
        (((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) →
        (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = ((γ • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) → (h : G) = γ :=
      fun h γ e1 e2 => hinjG _ _ e1 e2
    have one_case : ∀ h : MulAction.stabilizer G 𝔓,
        (((h : G) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) → (((h : G) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q → h = 1 := by
      intro h e1 e2
      have : (h : G) = 1 := idG h 1 (by rw [e1, one_smul]) (by rw [e2, one_smul])
      exact Subtype.ext this
    intro h
    rcases hvals h with ⟨e1, e2⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
    · exact Or.inl (one_case h e1 e2)
    ·
      obtain ⟨s1, s2⟩ := hσ0 h0
      have g1 : ((γ₀ • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ := pμ.trans s1
      have g2 : ((γ₀ • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ := pμq.trans s2
      have g1L : ((γ₀ • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ := by
        have t := g1; rw [smulB_coe] at t; exact t
      have g2L : ((γ₀ • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ := by
        have t := g2; rw [smulB_coe] at t; exact t
      obtain ⟨q1, q2⟩ := ModularCurve.Ws35FIXA.smul_smul_generators_of_smul_eq_subst4 q K γ₀ g1L g2L
      have g1' : (((γ₀ ^ 2) • (⟨lambdaModC (AlgebraicClosure ℚ), hμB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ := (psq _).trans q1
      have g2' : (((γ₀ ^ 2) • (⟨lambdaNModC (AlgebraicClosure ℚ) q, hμqB⟩ : ↥B) : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ := (psq _).trans q2
      rcases hrest with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · right; left
        exact Subtype.ext (idG h γ₀ (e1.trans g1.symm) (e2.trans g2.symm))
      · right; right
        exact Subtype.ext (idG h (γ₀ ^ 2) (e1.trans g1'.symm) (e2.trans g2'.symm))
    ·
      right; left
      rcases hσ1728 h0 with ⟨c, s1, s2⟩ | ⟨c, s1, s2⟩ | ⟨c, s1, s2⟩ <;>
        rcases hrest with ⟨c', e1, e2⟩ | ⟨c', e1, e2⟩ | ⟨c', e1, e2⟩

      · exact Subtype.ext (idG h γ₀ (e1.trans (pμ.trans s1).symm) (e2.trans (pμq.trans s2).symm))
      · exfalso; exact h3k (by linear_combination (2 : k) * c - c')
      · exfalso; exact h3k (by linear_combination c - (2 : k) * c')
      · exfalso; exact h3k (by linear_combination (2 : k) * c' - c)
      · exact Subtype.ext (idG h γ₀ (e1.trans (pμ.trans s1).symm) (e2.trans (pμq.trans s2).symm))
      · exfalso; exact h3k (by linear_combination c - (4 : k) * c')
      · exfalso; exact h3k (by linear_combination c' - (2 : k) * c)
      · exfalso; exact h3k (by linear_combination c' - (4 : k) * c)
      · exact Subtype.ext (idG h γ₀ (e1.trans (pμ.trans s1).symm) (e2.trans (pμq.trans s2).symm))
  have K3 : ∀ z : AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S,
      (∀ h : MulAction.stabilizer G 𝔓, T (AdicCompletion.stabAut ↥A' ↥B G 𝔓 h (T.symm z)) = z) ↔ ĝ z = z := by
    intro z
    constructor
    · intro H; rw [← hK3id]; exact H s₀
    · intro H h
      have h1 : AdicCompletion.stabAut ↥A' ↥B G 𝔓 1 = AlgEquiv.refl :=
        (AdicCompletion.stabilizerToCompletionAut ↥A' ↥B G 𝔓).map_one
      have h2 : AdicCompletion.stabAut ↥A' ↥B G 𝔓 (s₀ ^ 2)
          = (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀).trans (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀) := by
        rw [pow_two]
        exact (AdicCompletion.stabilizerToCompletionAut ↥A' ↥B G 𝔓).map_mul s₀ s₀
      rcases hgen h with rfl | rfl | rfl
      · simp [h1]
      · exact (hK3id z).trans H
      · rw [h2, AlgEquiv.trans_apply]
        have := hK3id z
        rw [H] at this

        have step : T (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀ (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀ (T.symm z)))
            = ĝ (T (AdicCompletion.stabAut ↥A' ↥B G 𝔓 s₀ (T.symm z))) := by
          rw [← hK3id (T _), RingEquiv.symm_apply_apply]
        rw [step, this, H]

  have K5 : (IsLocalRing.maximalIdeal ↥S).comap (Subring.inclusion hAS) = IsLocalRing.maximalIdeal ↥A' := by
    rw [hmaxA]
    ext z
    simp only [Ideal.mem_comap, Ideal.under_def, h𝔓def]
    rfl
  have K6 : ∀ z : ↥A', ∃ o : ↥(coeffSubring A K),
      z - ⟨φ (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o)),
            hRA _ (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _)⟩
        ∈ IsLocalRing.maximalIdeal ↥A' := by
    intro z
    obtain ⟨o, ho⟩ := ModularCurve.LambdaNodeLocalized.exists_sub_const_mem_maximalIdeal_lambdaLocalizedAtPoint
      hq2 red K l hl2 y hy (Subring.inclusion hAS z)
    refine ⟨o, ?_⟩
    rw [← K5, Ideal.mem_comap]

    have hconst : Subring.inclusion hAS
        (z - ⟨φ (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o)),
            hRA _ (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _)⟩)
        = Subring.inclusion hAS z - ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
            lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ := by
      rw [map_sub]
      congr 1
      refine Subtype.ext ?_
      show φ (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o)) = lambdaEval q (coeffSubring A K) (MvPolynomial.C o)
      simp only [modularEval, lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, CharPReduction.constSeries,
        RingHom.coe_comp, Function.comp_apply]
      exact ModularCurve.Ws35FIXA.qExpand_algebraMap 2 _
    rw [hconst]
    exact ho

  let Fx := FixedPoints.subalgebra ↥A' (AdicCompletion 𝔓 ↥B) (MulAction.stabilizer G 𝔓)
  let EL : Subring (AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S) :=
    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥S) ↥S →+* _).eqLocus (RingHom.id _)
  have hTmem : ∀ x : ↥Fx, T (x : AdicCompletion 𝔓 ↥B) ∈ EL := fun x => by
    show ĝ (T x) = T x
    refine (K3 (T x)).mp fun h => ?_
    rw [RingEquiv.symm_apply_apply]
    exact congrArg T (x.2 h)
  let Tfix : ↥Fx →+* ↥EL := (T.toRingHom.comp Fx.val.toRingHom).codRestrict EL hTmem
  have hTfix_bij : Function.Bijective Tfix := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have : T x = T y := congrArg Subtype.val hxy
      exact Subtype.ext (T.injective this)
    · refine ⟨⟨T.symm z, fun h => ?_⟩, Subtype.ext (by show T (T.symm z) = z; exact T.apply_symm_apply z)⟩
      have hz : ĝ z = z := z.2
      have := (K3 z).mpr hz h
      have h__af := congrArg T.symm this
      simp at h__af
      exact h__af
  refine ⟨A', hRA, hAS, locA, noethA, finRA, K5, K6, eInv.trans (RingEquiv.ofBijective Tfix hTfix_bij), fun z => ?_⟩

  show T ((((eInv (algebraMap ↥A' (AdicCompletion (IsLocalRing.maximalIdeal ↥A') ↥A') z)) : ↥Fx) :
      AdicCompletion 𝔓 ↥B)) = _
  have key : (((eInv (algebraMap ↥A' (AdicCompletion (IsLocalRing.maximalIdeal ↥A') ↥A') z)) : ↥Fx) :
      AdicCompletion 𝔓 ↥B) = algebraMap ↥B (AdicCompletion 𝔓 ↥B) (algebraMap ↥A' ↥B z) := by
    show AdicCompletion.invariantsCompletionHom ↥A' ↥B G (IsLocalRing.maximalIdeal ↥A') 𝔓
        (algebraMap ↥A' (AdicCompletion (IsLocalRing.maximalIdeal ↥A') ↥A') z) = _
    rw [AlgHom.commutes]
    rfl
  rw [key, hT]
  rfl

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ6 : ∀ x : ↥(lambdaFieldOver q K), σ^[6] x = x)
    (hσ0 : a = 0 →
        ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
         (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))
    (hσ1728 : a = 1728 →
        ((16 * l = -1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (32 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (8 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹)))
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))] [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    (hSF : (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ (lambdaFieldOver q K).toSubring)
    (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hg : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), ((g z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((σ ⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hSF z.2⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)))
    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hĝ : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), ĝ (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ z) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (g z)) :
    ∃ (A' : Subring (LaurentSeries (AlgebraicClosure ℚ)))
      (hRA : ∀ z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q), qExpand (AlgebraicClosure ℚ) 2 z ∈ A')
      (hAS : A' ≤ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
      (_ : IsLocalRing ↥A') (_ : IsNoetherianRing ↥A'),

      (letI : Algebra ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥A' :=
        (((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).codRestrict A'
          (fun z => hRA z z.2)).toAlgebra
       Module.Finite ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥A') ∧

      (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hAS) = IsLocalRing.maximalIdeal ↥A' ∧

      (∀ z : ↥A', ∃ o : ↥(coeffSubring A K),
        z - ⟨qExpand (AlgebraicClosure ℚ) 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o)),
              hRA _ (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _)⟩
          ∈ IsLocalRing.maximalIdeal ↥A') ∧

      ∃ eA : AdicCompletion (IsLocalRing.maximalIdeal ↥A') ↥A' ≃+*
          ↥((ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) →+* _).eqLocus (RingHom.id _)),
        ∀ z : ↥A', ((eA (algebraMap ↥A' _ z) : ↥((ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) →+* _).eqLocus (RingHom.id _))) :
            AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (Subring.inclusion hAS z) :=
  ModularCurve.Ws35FIXA.mainFIXA hq red a ha ha2 h01728 K ϖ hϖ l hla y hy σ hσK hσ6 hσ0 hσ1728 hSF g hg ĝ hĝ

end S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_subring_adicCompletion_ringEquiv_eqLocus_of_stabilizer_of_eq_zero_or_eq_1728 (solution)
