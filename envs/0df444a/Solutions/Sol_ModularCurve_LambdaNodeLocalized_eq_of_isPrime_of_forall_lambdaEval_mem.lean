-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.eq_of_isPrime_of_forall_lambdaEval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4e6e0e25-9fab-55a0-8c77-db1a49597d43

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_mul_eq_of_mem_lambdaFieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_eq_of_isPrime_of_forall_lambdaEval_mem
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_eq_of_isPrime_of_forall_lambdaEval_mem.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single jqModC jqNModC map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet qExpand_two_jq_mul_lambdaModC_sq isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace LambdaD2shared

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Transport

theorem laurentMap_lambdaModC (ι : ℚ →+* Qb) : laurentMap ι (lambdaModC ℚ) = lambdaModC Qb := by
  show laurentMap ι (laurentMap (Int.castRingHom ℚ) lambdaInt) = laurentMap (Int.castRingHom Qb) lambdaInt
  rw [laurentMap_laurentMap, RingHom.ext_int (ι.comp (Int.castRingHom ℚ)) (Int.castRingHom Qb)]

theorem laurentMap_qExpand_jq (ι : ℚ →+* Qb) : laurentMap ι (qExpand ℚ 2 jq) = qExpand Qb 2 (jqModC Qb) := by
  rw [laurentMap_qExpand]
  congr 1
  exact map_jqModC ι

theorem sextic_LQ : qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, laurentMap_lambdaModC,
    laurentMap_qExpand_jq] at h
  exact h

theorem sextic_LQ_q (q : ℕ) [Fact q.Prime] :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) sextic_LQ
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat] at h
  have h1 : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    show qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (qExpand Qb (1 * q) (jqModC Qb))
    rw [qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  have h2 : qExpand Qb q (lambdaModC Qb) = lambdaNModC Qb q := rfl
  rw [h1, h2] at h
  exact h

end Transport

section Values

variable {k : Type*} [Field k]

theorem two_five_six_ne_zero (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) [CharP k q] : (256 : k) ≠ 0 := by
  have h : ((256 : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k q]
    intro hdvd
    have h2 : q ∣ 2 := (Fact.out : q.Prime).dvd_of_dvd_pow (show q ∣ 2 ^ 8 by norm_num; exact hdvd)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  exact_mod_cast h

theorem level_two_value_aux (h256 : (256 : k) ≠ 0) (a l : k)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    l ≠ 0 ∧ 16 * l ≠ 1 ∧ a * (l ^ 2 * (16 * l - 1) ^ 2) = (256 * l ^ 2 - 16 * l + 1) ^ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply h256
    linear_combination -hy
  · intro h16
    apply h256
    linear_combination (256 * a * l ^ 2 * (16 * l - 1) - 256 * (16 * l) * (((16 * l) ^ 2 - 16 * l + 1) ^ 2 +
      ((16 * l) ^ 2 - 16 * l + 1) + 1)) * h16 - hy
  · apply mul_left_cancel₀ h256
    linear_combination hy

theorem level_two_value_pow (q : ℕ) [Fact q.Prime] [CharP k q] (a l : k)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    a ^ q * ((16 * l ^ q) ^ 2 * (16 * l ^ q - 1) ^ 2) = 256 * ((16 * l ^ q) ^ 2 - 16 * l ^ q + 1) ^ 3 := by
  have h := congrArg (frobenius k q) hy
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, frobenius_def] at h
  exact h

end Values

section Presentation

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
variable (A₀ : Subring Qb) (red₀ : ↥A₀ →+* k) (a l : k)

def denPoly (i : Fin 2) : MvPolynomial (Fin 2) ↥A₀ :=
  MvPolynomial.X i ^ 2 * (16 * MvPolynomial.X i - 1) ^ 2

def numPoly (i : Fin 2) : MvPolynomial (Fin 2) ↥A₀ :=
  (256 * MvPolynomial.X i ^ 2 - 16 * MvPolynomial.X i + 1) ^ 3

omit [Fact q.Prime] [CharP k q] in
theorem pointEval_X' (b b' : k) (i : Fin 2) : pointEval A₀ red₀ b b' (MvPolynomial.X i) = ![b, b'] i := by
  rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

theorem lambdaEval_X' (i : Fin 2) :
    lambdaEval q A₀ (MvPolynomial.X i) = ![lambdaModC Qb, lambdaNModC Qb q] i := by
  rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

theorem qExpand_modularEval_X' (i : Fin 2) :
    qExpand Qb 2 (modularEval (1 * q) A₀ (MvPolynomial.X i)) =
      ![qExpand Qb 2 (jqModC Qb), qExpand Qb 2 (jqNModC Qb (1 * q))] i := by
  rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  fin_cases i <;> rfl

theorem qExpand_modularEval_C (c : ↥A₀) :
    qExpand Qb 2 (modularEval (1 * q) A₀ (MvPolynomial.C c)) = lambdaEval q A₀ (MvPolynomial.C c) := by
  rw [modularEval, lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_C]
  show qExpand Qb 2 (algebraMap Qb LQ (c : Qb)) = algebraMap Qb LQ (c : Qb)
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem qExpand_modularEval_X_mul_den (i : Fin 2) :
    qExpand Qb 2 (modularEval (1 * q) A₀ (MvPolynomial.X i)) * lambdaEval q A₀ (denPoly A₀ i) =
      lambdaEval q A₀ (numPoly A₀ i) := by
  simp only [denPoly, numPoly, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, lambdaEval_X',
    qExpand_modularEval_X']
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    linear_combination sextic_LQ
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination sextic_LQ_q q

theorem pointEval_den_ne_zero (hq : 5 ≤ q)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) (i : Fin 2) :
    pointEval A₀ red₀ l (l ^ q) (denPoly A₀ i) ≠ 0 := by
  have h256 := two_five_six_ne_zero (k := k) q hq
  obtain ⟨hl0, hl1, -⟩ := level_two_value_aux h256 a l hy
  obtain ⟨hlq0, hlq1, -⟩ := level_two_value_aux h256 (a ^ q) (l ^ q) (level_two_value_pow q a l hy)
  simp only [denPoly, map_mul, map_pow, map_sub, map_one, map_ofNat, pointEval_X']
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact mul_ne_zero (pow_ne_zero _ hlq0) (pow_ne_zero _ (sub_ne_zero.mpr hlq1))

theorem pointEval_num (hq : 5 ≤ q)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) (i : Fin 2) :
    pointEval A₀ red₀ l (l ^ q) (numPoly A₀ i) =
      ![a, a ^ q] i * pointEval A₀ red₀ l (l ^ q) (denPoly A₀ i) := by
  have h256 := two_five_six_ne_zero (k := k) q hq
  obtain ⟨-, -, h0⟩ := level_two_value_aux h256 a l hy
  obtain ⟨-, -, h1⟩ := level_two_value_aux h256 (a ^ q) (l ^ q) (level_two_value_pow q a l hy)
  simp only [denPoly, numPoly, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, pointEval_X']
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [h0]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h1]

theorem exists_presentation (hq : 5 ≤ q)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (p : MvPolynomial (Fin 2) ↥A₀) :
    ∃ P M : MvPolynomial (Fin 2) ↥A₀, pointEval A₀ red₀ l (l ^ q) M ≠ 0 ∧
      qExpand Qb 2 (modularEval (1 * q) A₀ p) * lambdaEval q A₀ M = lambdaEval q A₀ P ∧
      pointEval A₀ red₀ l (l ^ q) P = pointEval A₀ red₀ l (l ^ q) M * pointEval A₀ red₀ a (a ^ q) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c, 1, by rw [map_one]; exact one_ne_zero, ?_, ?_⟩
    · rw [map_one, mul_one, qExpand_modularEval_C]
    · rw [map_one, one_mul, pointEval, pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
  | add p r hp hr =>
    obtain ⟨P₁, M₁, hM₁, h₁, e₁⟩ := hp
    obtain ⟨P₂, M₂, hM₂, h₂, e₂⟩ := hr
    refine ⟨P₁ * M₂ + P₂ * M₁, M₁ * M₂, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hM₁ hM₂
    · simp only [map_add, map_mul]
      linear_combination lambdaEval q A₀ M₂ * h₁ + lambdaEval q A₀ M₁ * h₂
    · simp only [map_add, map_mul]
      rw [e₁, e₂]
      ring
  | mul_X p i hp =>
    obtain ⟨P, M, hM, h, e⟩ := hp
    refine ⟨P * numPoly A₀ i, M * denPoly A₀ i, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hM (pointEval_den_ne_zero A₀ red₀ a l hq hy i)
    · simp only [map_mul]
      linear_combination (qExpand Qb 2 (modularEval (1 * q) A₀ (MvPolynomial.X i)) * lambdaEval q A₀ (denPoly A₀ i)) * h
        + lambdaEval q A₀ P * qExpand_modularEval_X_mul_den (q := q) A₀ i
    · simp only [map_mul]
      rw [e, pointEval_num A₀ red₀ a l hq hy i, pointEval_X']
      ring

theorem qExpand_two_mem_lambdaLocalizedAtPoint (hq : 5 ≤ q)
    (hy : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    {f : LQ} (hf : f ∈ modularLocalizedAtPoint (1 * q) A₀ red₀ a (a ^ q)) :
    qExpand Qb 2 f ∈ lambdaLocalizedAtPoint q A₀ red₀ l (l ^ q) := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  obtain ⟨R, Mr, hMr, hR, eR⟩ := exists_presentation A₀ red₀ a l hq hy r
  obtain ⟨S, Ms, hMs, hS, eS⟩ := exists_presentation A₀ red₀ a l hq hy s
  refine ⟨R * Ms, S * Mr, ?_, ?_⟩
  · rw [map_mul, eS]
    exact mul_ne_zero (mul_ne_zero hMs hs) hMr
  · have h := congrArg (qExpand Qb 2) hfs
    rw [map_mul] at h
    simp only [map_mul]
    linear_combination (lambdaEval q A₀ Ms * lambdaEval q A₀ Mr) * h
      - (qExpand Qb 2 f * lambdaEval q A₀ Mr) * hS + lambdaEval q A₀ Ms * hR

end Presentation

section Integral

theorem isIntegral_of_isIntegralElem_comp {S : Type*} [CommRing S] (R : Subring LQ) (g : S →+* LQ)
    (hg : ∀ s, g s ∈ R) {x : LQ} (hx : g.IsIntegralElem x) : IsIntegral ↥R x := by
  obtain ⟨P, hPm, hPev⟩ := hx
  refine ⟨P.map (g.codRestrict R hg), hPm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hPev

theorem mem_of_isIntegral_of_isIntegrallyClosed (R : Subring LQ) (hic : IsIntegrallyClosed ↥R) {x : LQ}
    (hfrac : ∃ u v : LQ, u ∈ R ∧ v ∈ R ∧ v ≠ 0 ∧ x * v = u) (hint : IsIntegral ↥R x) : x ∈ R := by
  classical
  obtain ⟨u, v, hu, hv, hv0, hxv⟩ := hfrac
  have hinj : Function.Injective (algebraMap ↥R LQ) := Subtype.val_injective
  let φ : FractionRing ↥R →ₐ[↥R] LQ :=
    { IsFractionRing.lift hinj with commutes' := fun r => IsFractionRing.lift_algebraMap hinj r }
  have hφ : Function.Injective φ := φ.toRingHom.injective
  let w : FractionRing ↥R := algebraMap ↥R _ ⟨u, hu⟩ / algebraMap ↥R _ ⟨v, hv⟩
  have hw : φ w = x := by
    have h1 : φ (algebraMap ↥R _ ⟨u, hu⟩) = u := IsFractionRing.lift_algebraMap hinj _
    have h2 : φ (algebraMap ↥R _ ⟨v, hv⟩) = v := IsFractionRing.lift_algebraMap hinj _
    rw [map_div₀, h1, h2, div_eq_iff hv0, hxv]
  have hwint : IsIntegral ↥R w := by
    rw [← isIntegral_algHom_iff φ hφ, hw]; exact hint
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R) (K := FractionRing ↥R)).mp hwint
  have : (r : LQ) = x := by
    rw [← hw, ← hr]; exact (IsFractionRing.lift_algebraMap hinj r).symm
  rw [← this]; exact r.2

end Integral

section Markers

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k]
variable (A₀ : Subring Qb) (red₀ : ↥A₀ →+* k) (y : ↥A₀)

omit [Fact q.Prime] in

theorem pointEval_eq_redRestrict_eval (n : ℕ) (p : MvPolynomial (Fin 2) ↥A₀) :
    pointEval A₀ red₀ (red₀ y) (red₀ y ^ n) p = red₀ (MvPolynomial.eval ![y, y ^ n] p) := by
  have : pointEval A₀ red₀ (red₀ y) (red₀ y ^ n) = red₀.comp (MvPolynomial.eval₂Hom (RingHom.id _) ![y, y ^ n]) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp [pointEval]
    · fin_cases i <;> simp [pointEval]
  rw [this]
  rfl

theorem eq_of_isPrime_of_forall_marker_mem
    (hunit : ∀ c : ↥A₀, red₀ c ≠ 0 → IsUnit c)
    (B : Subring LQ)
    (hBR : ∀ b ∈ B, b ∈ lambdaLocalizedAtPoint q A₀ red₀ (red₀ y) (red₀ y ^ q))
    (hTB : ∀ p : MvPolynomial (Fin 2) ↥A₀, lambdaEval q A₀ p ∈ B)
    (P₁ P₂ : Ideal ↥B) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : ∀ p : MvPolynomial (Fin 2) ↥A₀, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p = 0 →
      (⟨lambdaEval q A₀ p, hTB p⟩ : ↥B) ∈ P₁)
    (h₂ : ∀ p : MvPolynomial (Fin 2) ↥A₀, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p = 0 →
      (⟨lambdaEval q A₀ p, hTB p⟩ : ↥B) ∈ P₂) :
    P₁ = P₂ := by
  classical
  let LB : MvPolynomial (Fin 2) ↥A₀ →+* ↥B := (lambdaEval q A₀).codRestrict B hTB
  have hLB : ∀ p, (⟨lambdaEval q A₀ p, hTB p⟩ : ↥B) = LB p := fun p => rfl

  have key : ∀ (P : Ideal ↥B), P ≠ ⊤ →
      (∀ p, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p = 0 → LB p ∈ P) →
      ∀ p, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p ≠ 0 → LB p ∉ P := by
    intro P hP hmark p hp hpP
    set c : ↥A₀ := MvPolynomial.eval ![y, y ^ q] p with hc
    have hcu : IsUnit c := hunit c (by rw [← pointEval_eq_redRestrict_eval]; exact hp)
    have hmarker : LB (p - MvPolynomial.C c) ∈ P := hmark _ (by
      rw [map_sub, pointEval_eq_redRestrict_eval, sub_eq_zero, pointEval, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C])
    rw [map_sub] at hmarker
    have hCc : LB (MvPolynomial.C c) ∈ P := by
      have := P.sub_mem hpP hmarker
      rwa [sub_sub_cancel] at this
    exact hP (Ideal.eq_top_of_isUnit_mem P hCc ((hcu.map MvPolynomial.C).map LB))

  have incl : ∀ (P P' : Ideal ↥B) [P.IsPrime] [P'.IsPrime],
      (∀ p, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p = 0 → LB p ∈ P) →
      (∀ p, pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) p = 0 → LB p ∈ P') → P ≤ P' := by
    intro P P' _ _ hP hP' b hb
    obtain ⟨r, s, hs, hbs⟩ := hBR b b.2
    have hbs' : b * LB s = LB r := Subtype.ext hbs
    by_cases hr : pointEval A₀ red₀ (red₀ y) (red₀ y ^ q) r = 0
    · have h1 : b * LB s ∈ P' := by rw [hbs']; exact hP' r hr
      rcases Ideal.IsPrime.mem_or_mem ‹P'.IsPrime› h1 with h | h
      · exact h
      · exact absurd h (key P' (Ideal.IsPrime.ne_top ‹_›) hP' s hs)
    · exfalso
      have h1 : LB r ∈ P := by rw [← hbs']; exact P.mul_mem_right _ hb
      exact key P (Ideal.IsPrime.ne_top ‹_›) hP r hr h1
  exact le_antisymm (incl P₁ P₂ (fun p hp => h₁ p hp) (fun p hp => h₂ p hp))
    (incl P₂ P₁ (fun p hp => h₂ p hp) (fun p hp => h₁ p hp))

end Markers

end LambdaD2shared
end ModularCurve

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single jqModC jqNModC map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet qExpand_two_jq_mul_lambdaModC_sq isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace LambdaD2c

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem redRestrict_ne_zero_of_isUnit (red : A →+* k) (K : IntermediateField ℚ Qb)
    (c : ↥(coeffSubring A K)) (hu : IsUnit c) : redRestrict red K c ≠ 0 := by
  intro h0
  have := hu.map (redRestrict red K)
  rw [h0] at this
  exact not_isUnit_zero this

theorem isUnit_of_redRestrict_ne_zero (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) : IsUnit c := by
  have hc0 : (c : Qb) ≠ 0 := by
    rintro h0
    apply hc
    rw [show c = 0 from Subtype.ext h0, map_zero]
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · have hcK : (c : Qb) ∈ K := h.le c.2
    have hinv : (c : Qb)⁻¹ ∈ coeffSubring A K := h.ge (K.inv_mem hcK)
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  · haveI := h
    have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h0
      push_cast at h1
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h1
    have hker : RingHom.ker (redRestrict red K) ≠ ⊥ := by
      intro hbot
      have h1 : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      rw [hbot, Ideal.mem_bot] at h1
      exact hq0 h1
    haveI : (RingHom.ker (redRestrict red K)).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker (redRestrict red K)).IsMaximal := IsPrime.to_maximal_ideal hker
    have heq : RingHom.ker (redRestrict red K) = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
    by_contra hu
    have h1 : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [← heq, RingHom.mem_ker] at h1
    exact hc h1

theorem main {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy2 : redRestrict red K y ^ (q ^ 2) = redRestrict red K y)
    (hy : a * ((16 * redRestrict red K y) ^ 2 * (16 * redRestrict red K y - 1) ^ 2)
      = 256 * ((16 * redRestrict red K y) ^ 2 - 16 * redRestrict red K y + 1) ^ 3)
    (B : Subring LQ)
    (hBL : B ≤ (lambdaFieldOver q K).toSubring)
    (hTB : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B)
    (hint : ∀ x ∈ B, ((qExpand Qb 2).comp
      (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y) (redRestrict red K y ^ q) p = 0 →
        (⟨lambdaEval q (coeffSubring A K) p, hTB p⟩ : ↥B) ∈ P₁)
    (h₂ : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y) (redRestrict red K y ^ q) p = 0 →
        (⟨lambdaEval q (coeffSubring A K) p, hTB p⟩ : ↥B) ∈ P₂) :
    P₁ = P₂ := by
  have h256 := LambdaD2shared.two_five_six_ne_zero (k := k) q hq
  obtain ⟨hl0, hl1, -⟩ := LambdaD2shared.level_two_value_aux h256 a (redRestrict red K y) hy

  have hic := ModularCurve.isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring hq red (redRestrict red K y) hy2
    hl0 hl1 ⟨a, ha, hy⟩ K ⟨y, rfl⟩

  have hBR : ∀ b ∈ B, b ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K)
      (redRestrict red K y) (redRestrict red K y ^ q) := fun b hb =>
    LambdaD2shared.mem_of_isIntegral_of_isIntegrallyClosed _ hic
      (ModularCurve.LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver red (redRestrict red K y) K (hBL hb))
      (LambdaD2shared.isIntegral_of_isIntegralElem_comp _
        ((qExpand Qb 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype)
        (fun s => LambdaD2shared.qExpand_two_mem_lambdaLocalizedAtPoint (coeffSubring A K) (redRestrict red K) a
          (redRestrict red K y) hq hy s.2)
        (hint b hb))

  exact LambdaD2shared.eq_of_isPrime_of_forall_marker_mem (coeffSubring A K) (redRestrict red K) y
    (fun c hc => isUnit_of_redRestrict_ne_zero q red K c hc) B hBR hTB P₁ P₂ h₁ h₂

end LambdaD2c
end ModularCurve

end

theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy2 : redRestrict red K y ^ (q ^ 2) = redRestrict red K y)
    (hy : a * ((16 * redRestrict red K y) ^ 2 * (16 * redRestrict red K y - 1) ^ 2)
      = 256 * ((16 * redRestrict red K y) ^ 2 - 16 * redRestrict red K y + 1) ^ 3)
    (B : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hBL : B ≤ (lambdaFieldOver q K).toSubring)
    (hRB : ∀ x ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q),
      qExpand (AlgebraicClosure ℚ) 2 x ∈ B)
    (hTB : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B)
    (hint : ∀ x ∈ B, ((qExpand (AlgebraicClosure ℚ) 2).comp
      (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y) (redRestrict red K y ^ q) p = 0 →
        (⟨lambdaEval q (coeffSubring A K) p, hTB p⟩ : ↥B) ∈ P₁)
    (h₂ : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y) (redRestrict red K y ^ q) p = 0 →
        (⟨lambdaEval q (coeffSubring A K) p, hTB p⟩ : ↥B) ∈ P₂) :
    P₁ = P₂ :=
  ModularCurve.LambdaD2c.main hq red a ha K y hy2 hy B hBL hTB hint P₁ P₂ h₁ h₂

end S_ModularCurve_LambdaNodeLocalized_eq_of_isPrime_of_forall_lambdaEval_mem
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_eq_of_isPrime_of_forall_lambdaEval_mem (solution)
