-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d710b0cb-ad44-574e-aed1-ccd02f1a7383

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem.ModularCurve ModularCurve.NodeLocalized~sub_C_eval_mem_span ModularCurve.LambdaNodeLocalized"

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.pointEval qExpand ssJSet LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
namespace OrbLoc
p2m_open "ModularCurve"

open IsLocalRing

theorem sub_C_eval_mem_span {R : Type*} [CommRing R] (x y : R) (p : MvPolynomial (Fin 2) R) :
    p - MvPolynomial.C (MvPolynomial.eval ![x, y] p) ∈
      Ideal.span ({MvPolynomial.X 0 - MvPolynomial.C x, MvPolynomial.X 1 - MvPolynomial.C y} :
        Set (MvPolynomial (Fin 2) R)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have : p + r - MvPolynomial.C (MvPolynomial.eval ![x, y] (p + r)) =
        (p - MvPolynomial.C (MvPolynomial.eval ![x, y] p)) + (r - MvPolynomial.C (MvPolynomial.eval ![x, y] r)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p i hp =>
    have hXi : (MvPolynomial.X i : MvPolynomial (Fin 2) R) - MvPolynomial.C (![x, y] i) ∈
        Ideal.span ({MvPolynomial.X 0 - MvPolynomial.C x, MvPolynomial.X 1 - MvPolynomial.C y} :
          Set (MvPolynomial (Fin 2) R)) := by
      fin_cases i
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    have : p * MvPolynomial.X i - MvPolynomial.C (MvPolynomial.eval ![x, y] (p * MvPolynomial.X i)) =
        (p - MvPolynomial.C (MvPolynomial.eval ![x, y] p)) * MvPolynomial.X i +
          MvPolynomial.C (MvPolynomial.eval ![x, y] p) * (MvPolynomial.X i - MvPolynomial.C (![x, y] i)) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hXi)

theorem isUnit_of_redRestrict_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} (q : ℕ) [Fact q.Prime]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {c : ↥(coeffSubring A K)} (hc : redRestrict red K c ≠ 0) : IsUnit c := by
  have hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := by
    rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
    · exfalso
      have hqK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
        rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K)
      have h1 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) * redRestrict red K ⟨_, hqK⟩ = 1 := by
        rw [← map_mul, ← map_one (redRestrict red K)]
        congr 1
        apply Subtype.ext
        push_cast
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
      rw [map_natCast, CharP.cast_eq_zero, zero_mul] at h1
      exact zero_ne_one h1
    · exact h
  by_contra hu
  have hmem : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := hu
  have hker : (RingHom.ker (redRestrict red K)).IsMaximal := by
    have hprime : (RingHom.ker (redRestrict red K)).IsPrime := RingHom.ker_isPrime _
    have hne : RingHom.ker (redRestrict red K) ≠ ⊥ := by
      intro h0
      have hq : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      rw [h0, Ideal.mem_bot] at hq
      have hq' := congrArg Subtype.val hq
      push_cast at hq'
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq'
    exact hprime.isMaximal hne
  rw [← IsLocalRing.eq_maximalIdeal hker, RingHom.mem_ker] at hmem
  exact hc hmem

end ModularCurve.OrbLoc

open IsLocalRing in
theorem solution
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
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (Q : Ideal ↥B) (hQ : Q.IsMaximal)
    (l' : k) (hla' : a * ((16 * l') ^ 2 * (16 * l' - 1) ^ 2) = 256 * ((16 * l') ^ 2 - 16 * l' + 1) ^ 3)
    (y' : ↥(coeffSubring A K)) (hy' : redRestrict red K y' = l')
    (hϖQ : ∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ) → b ∈ Q)
    (hμQ : ∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y') → b ∈ Q)
    (hμqQ : ∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y' ^ q)) → b ∈ Q) :
    ∃ (hBS' : B ≤ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q))
      (_ : IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q))),
      Q = (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q))).comap
            (Subring.inclusion hBS') := by
  classical
  have hqp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hl2' : l' ^ (q ^ 2) = l' := pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l' hla'
  obtain ⟨-, hLoc', -, -⟩ :=
    ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring hq2 red l' hl2' K y' hy' ϖ hϖ
  haveI := hLoc'
  obtain ⟨hRB, hpolyB, hBS', hPmax, hloc, hmark⟩ :=
    ModularCurve.LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem hq red a ha ha2 h01728 K
      l' hla' y' hy' B hB
  refine ⟨hBS', hLoc', ?_⟩

  let ΛB : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥B :=
    (lambdaEval q (coeffSubring A K)).codRestrict B hpolyB
  let ΛS : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q)) :=
    (lambdaEval q (coeffSubring A K)).codRestrict _
      (lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q))
  have hincl : ∀ p, Subring.inclusion hBS' (ΛB p) = ΛS p := fun p => rfl
  have hval : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l' (l' ^ q) p =
        redRestrict red K (MvPolynomial.eval ![y', y' ^ q] p) := by
    intro p
    have hfun : (![l', l' ^ q] : Fin 2 → k) = (redRestrict red K) ∘ ![y', y' ^ q] := by
      funext i; fin_cases i <;> simp [hy']
    rw [NodeLocalized.pointEval, MvPolynomial.coe_eval₂Hom, hfun, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left, RingHom.comp_id]

  have hkerQ : Ideal.map ΛB (Ideal.span ({MvPolynomial.X 0 - MvPolynomial.C y', MvPolynomial.X 1 - MvPolynomial.C (y' ^ q)} :
      Set (MvPolynomial (Fin 2) ↥(coeffSubring A K)))) ≤ Q := by
    rw [Ideal.map_span, Ideal.span_le, Set.image_insert_eq, Set.image_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff, SetLike.mem_coe, SetLike.mem_coe]
    exact ⟨hμQ _ rfl, hμqQ _ rfl⟩

  have hQmem : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l' (l' ^ q) p = 0 → ΛB p ∈ Q := by
    intro p hp
    set p₀ := MvPolynomial.eval ![y', y' ^ q] p with hp₀
    have h1 : ΛB p - ΛB (MvPolynomial.C p₀) ∈ Q := by
      rw [← map_sub]; exact hkerQ (Ideal.mem_map_of_mem _ (ModularCurve.OrbLoc.sub_C_eval_mem_span y' (y' ^ q) p))
    have h2 : ΛB (MvPolynomial.C p₀) ∈ Q := by
      have hred : redRestrict red K p₀ = 0 := by rw [hp₀, ← hval]; exact hp
      obtain ⟨d, hd⟩ := (hϖ p₀).mp hred
      rw [hd, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (hϖQ _ rfl)
    have := add_mem h1 h2
    rwa [sub_add_cancel] at this

  have hunitS : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l' (l' ^ q) p ≠ 0 → IsUnit (ΛS p) := by
    intro p hp
    have h0 : lambdaEval q (coeffSubring A K) p ≠ 0 := fun h =>
      hp (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l' hl2' K p h)
    refine isUnit_iff_exists_inv.mpr ⟨⟨(lambdaEval q (coeffSubring A K) p)⁻¹, 1, p, hp, ?_⟩, ?_⟩
    · rw [map_one]; exact inv_mul_cancel₀ h0
    · exact Subtype.ext (mul_inv_cancel₀ h0)

  set P : Ideal ↥B := (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l' (l' ^ q))).comap (Subring.inclusion hBS') with hPdef
  suffices hPQ : P ≤ Q by exact (hPmax.eq_of_le hQ.ne_top hPQ).symm
  intro b hb
  have hbm : Subring.inclusion hBS' b ∈ IsLocalRing.maximalIdeal _ := hb
  obtain ⟨r, s, hs, hbrs⟩ := hBS' b.2

  have e1 : Subring.inclusion hBS' b * ΛS s = ΛS r := Subtype.ext hbrs

  have hr0 : NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l' (l' ^ q) r = 0 := by
    by_contra hr
    obtain ⟨ur, hur⟩ := hunitS r hr
    obtain ⟨us, hus⟩ := hunitS s hs
    have hbu : IsUnit (Subring.inclusion hBS' b) := by
      have : Subring.inclusion hBS' b = ↑ur * ↑us⁻¹ := by
        rw [hur, ← e1, ← hus, mul_assoc, Units.mul_inv, mul_one]
      rw [this]; exact (Units.isUnit _).mul (Units.isUnit _)
    exact (IsLocalRing.mem_maximalIdeal _).mp hbm hbu

  have hrQ : ΛB r ∈ Q := hQmem r hr0
  have e2 : b * ΛB s = ΛB r := Subtype.ext hbrs
  have hsQ : ΛB s ∉ Q := by
    intro hsQ

    set s₀ := MvPolynomial.eval ![y', y' ^ q] s with hs₀
    have h1 : ΛB s - ΛB (MvPolynomial.C s₀) ∈ Q := by
      rw [← map_sub]; exact hkerQ (Ideal.mem_map_of_mem _ (ModularCurve.OrbLoc.sub_C_eval_mem_span y' (y' ^ q) s))
    have h2 : ΛB (MvPolynomial.C s₀) ∈ Q := by
      have := sub_mem hsQ h1; rwa [sub_sub_cancel] at this
    have hs₀u : IsUnit s₀ := by
      apply ModularCurve.OrbLoc.isUnit_of_redRestrict_ne_zero q red K
      rw [hs₀, ← hval]; exact hs
    have hu : IsUnit (ΛB (MvPolynomial.C s₀)) := (hs₀u.map MvPolynomial.C).map ΛB
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu)
  have hprod : b * ΛB s ∈ Q := by rw [e2]; exact hrQ
  exact (hQ.isPrime.mem_or_mem hprod).resolve_right hsQ

end S_ModularCurve_LambdaNodeLocalized_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_eq_comap_maximalIdeal_lambdaLocalizedAtPoint_of_sub_const_mem (solution)
