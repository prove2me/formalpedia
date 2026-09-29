-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f18128a7-b045-5f14-a0ee-2c45935bb816

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion.ModularCurve ModularCurve.UVCrossingModel"
open ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet jWidth jWidth_pos jWidth_dvd_six uvCrossingIdeal UVCrossingModel UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const UVCrossingModel.constHom UVCrossingModel.constHom_apply LambdaNodeLocalized.exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel UVCrossingModel.exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent UVCrossingModel.isLocalRing_of_not_isUnit UVCrossingModel.isAdicComplete_maximalIdeal UVCrossingModel.U_mul_V NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"
namespace Ws30FixSigma

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

abbrev SL : Subring LQ :=
  lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q)

abbrev ev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(SL q A red a K) :=
  ⟨lambdaEval q (coeffSubring A K) p,
    lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q) p⟩

def evHom : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(SL q A red a K) :=
  (lambdaEval q (coeffSubring A K)).codRestrict (SL q A red a K)
    (lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q))

theorem evHom_apply (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : evHom q A red a K p = ev q A red a K p := rfl

private def _root_.ModularCurve.Ws30FixSigma.constHom : ↥(coeffSubring A K) →+* ↥(SL q A red a K) :=
  (evHom q A red a K).comp MvPolynomial.C

p2m_export "ModularCurve.Ws30FixSigma" "constHom"
private theorem _root_.ModularCurve.Ws30FixSigma.constHom_apply (c : ↥(coeffSubring A K)) :
    constHom q A red a K c = ev q A red a K (MvPolynomial.C c) := rfl

p2m_export "ModularCurve.Ws30FixSigma" "constHom_apply"
end Defs

section RedLemmas
variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem mem_coeffSubring_iff' (K : IntermediateField ℚ Qb) {x : Qb} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem red_eq_zero_of_mem_maximalIdeal (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem isUnit_coeffSubring_iff (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (c : ↥(coeffSubring A K)) : IsUnit c ↔ redRestrict red K c ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hc
    have h1 : redRestrict red K ((u * u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) = 1 := by
      rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hc, zero_mul] at h1
    exact zero_ne_one h1
  · intro hc
    have hcA : (c : Qb) ∈ A := ((mem_coeffSubring_iff' (A := A) K).mp c.2).1
    have hcK : (c : Qb) ∈ K := ((mem_coeffSubring_iff' (A := A) K).mp c.2).2
    have hcm : (⟨(c : Qb), hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun hm =>
      hc (red_eq_zero_of_mem_maximalIdeal red q _ hm)
    have hu : IsUnit (⟨(c : Qb), hcA⟩ : A) := by
      by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hu
    have hmul : (((u⁻¹ : Aˣ) : A) : Qb) * (c : Qb) = 1 := by
      have h := congrArg (fun z : A => (z : Qb)) u.inv_mul
      rw [hu] at h
      simpa using h
    have hinv : (c : Qb)⁻¹ = (((u⁻¹ : Aˣ) : A) : Qb) := inv_eq_of_mul_eq_one_left hmul
    have hinvmem : (c : Qb)⁻¹ ∈ coeffSubring A K :=
      (mem_coeffSubring_iff' (A := A) K).mpr ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, K.inv_mem hcK⟩
    have hc0 : (c : Qb) ≠ 0 := by
      rintro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this, map_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩

theorem stepA_dvr (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] : IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : Qb)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : Qb)⁻¹ ∈ K)
    have hu : IsUnit (((q : ℕ) : ↥(coeffSubring A K))) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hqK⟩, Subtype.ext (by
        push_cast
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))⟩
    have := (isUnit_coeffSubring_iff red K q _).mp hu
    apply this
    rw [map_natCast, CharP.cast_eq_zero]
  · exact h

theorem stepA_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧ (∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) ∧
      ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hker : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
    intro c
    have h1 : redRestrict red K c = 0 ↔ ¬ IsUnit c := by
      rw [isUnit_coeffSubring_iff red K q c, not_not]
    rw [h1, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Iff.rfl
  refine ⟨ϖ, hϖ, hker, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

end RedLemmas

section PSQuot
variable {O : Type*} [CommRing O] (I : Ideal (PowerSeries O))

theorem exists_trunc_add_X_pow_mul (f : PowerSeries O) (N : ℕ) :
    ∃ g : PowerSeries O, f = (PowerSeries.trunc N f : PowerSeries O) + PowerSeries.X ^ N * g := by
  have h : PowerSeries.X ^ N ∣ f - (PowerSeries.trunc N f : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [← hg]; ring⟩

theorem ringHom_ext_of_isHausdorff {T : Type*} [CommRing T] (J : Ideal T) [IsHausdorff J T]
    (φ₁ φ₂ : (PowerSeries O ⧸ I) →+* T)
    (hC : ∀ o : O, φ₁ (Ideal.Quotient.mk I (PowerSeries.C o)) = φ₂ (Ideal.Quotient.mk I (PowerSeries.C o)))
    (hX : φ₁ (Ideal.Quotient.mk I PowerSeries.X) = φ₂ (Ideal.Quotient.mk I PowerSeries.X))
    (hJ : φ₁ (Ideal.Quotient.mk I PowerSeries.X) ∈ J) : φ₁ = φ₂ := by

  have hpoly : ∀ p : Polynomial O, φ₁ (Ideal.Quotient.mk I (p : PowerSeries O)) = φ₂ (Ideal.Quotient.mk I (p : PowerSeries O)) := by
    intro p
    have key : (φ₁.comp (Ideal.Quotient.mk I)).comp Polynomial.coeToPowerSeries.ringHom =
        (φ₂.comp (Ideal.Quotient.mk I)).comp Polynomial.coeToPowerSeries.ringHom := by
      refine Polynomial.ringHom_ext (fun o => ?_) ?_
      · simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC o
      · simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX
    have := congrArg (fun ψ => ψ p) key
    simpa [Polynomial.coeToPowerSeries.ringHom_apply] using this
  refine RingHom.ext fun w => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w

  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff J T) _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨g, hg⟩ := exists_trunc_add_X_pow_mul f N
  have h1 : φ₁ (Ideal.Quotient.mk I f) - φ₂ (Ideal.Quotient.mk I f) =
      φ₁ (Ideal.Quotient.mk I PowerSeries.X) ^ N * (φ₁ (Ideal.Quotient.mk I g) - φ₂ (Ideal.Quotient.mk I g)) := by
    conv_lhs => rw [hg]
    simp only [map_add, map_mul, map_pow]
    rw [hpoly, hX]
    ring
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hJ N)

end PSQuot

section Crossing
variable {W : Type*} [CommRing W] [IsLocalRing W] (π : W)

omit [IsLocalRing W] in
theorem const_eq_algebraMap' (w : W) : const π w = algebraMap W (UVCrossingModel W π) w := rfl

omit [IsLocalRing W] in
theorem const_sub' (a b : W) : const π (a - b) = const π a - const π b := map_sub (UVCrossingModel.constHom π) a b

theorem exists_residueHom (hπu : ¬ IsUnit π) :
    ∃ ρ : UVCrossingModel W π →+* ResidueField W,
      (∀ w, ρ (const π w) = residue W w) ∧ ρ (U π) = 0 ∧ ρ (V π) = 0 := by
  have hker : ∀ f ∈ uvCrossingIdeal W π, ((residue W).comp MvPowerSeries.constantCoeff) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hP : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π :
        MvPowerSeries (Fin 2) W) = -π := by
      rw [map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub]
    rw [RingHom.comp_apply, map_mul, hP, map_mul, map_neg, (residue_eq_zero_iff π).mpr
      ((mem_maximalIdeal π).mpr hπu), neg_zero, mul_zero]
  refine ⟨Ideal.Quotient.lift _ _ hker, fun w => ?_, ?_, ?_⟩
  · show Ideal.Quotient.lift _ _ hker (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = _
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_C]
  · show Ideal.Quotient.lift _ _ hker (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = _
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_X, map_zero]
  · show Ideal.Quotient.lift _ _ hker (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = _
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_X, map_zero]

variable [IsLocalRing (UVCrossingModel W π)]

theorem mem_maximalIdeal_iff_of_residueHom (ρ : UVCrossingModel W π →+* ResidueField W)
    (hρ : ∀ w, ρ (const π w) = residue W w) (z : UVCrossingModel W π) :
    z ∈ maximalIdeal (UVCrossingModel W π) ↔ ρ z = 0 := by
  have hsurj : Function.Surjective ρ := by
    intro r
    obtain ⟨w, rfl⟩ := residue_surjective r
    exact ⟨const π w, hρ w⟩
  have hmax : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hsurj
  rw [← eq_maximalIdeal hmax, RingHom.mem_ker]

theorem U_mem_maximalIdeal (hπu : ¬ IsUnit π) : U π ∈ maximalIdeal (UVCrossingModel W π) := by
  obtain ⟨ρ, hρ, hU, -⟩ := exists_residueHom π hπu
  exact (mem_maximalIdeal_iff_of_residueHom π ρ hρ _).mpr hU

theorem V_mem_maximalIdeal (hπu : ¬ IsUnit π) : V π ∈ maximalIdeal (UVCrossingModel W π) := by
  obtain ⟨ρ, hρ, -, hV⟩ := exists_residueHom π hπu
  exact (mem_maximalIdeal_iff_of_residueHom π ρ hρ _).mpr hV

theorem const_mem_maximalIdeal_iff (hπu : ¬ IsUnit π) (w : W) :
    const π w ∈ maximalIdeal (UVCrossingModel W π) ↔ w ∈ maximalIdeal W := by
  obtain ⟨ρ, hρ, -, -⟩ := exists_residueHom π hπu
  rw [mem_maximalIdeal_iff_of_residueHom π ρ hρ, hρ, residue_eq_zero_iff]

theorem exists_sub_const_mem_maximalIdeal (hπu : ¬ IsUnit π) (z : UVCrossingModel W π) :
    ∃ w : W, z - const π w ∈ maximalIdeal (UVCrossingModel W π) := by
  obtain ⟨ρ, hρ, -, -⟩ := exists_residueHom π hπu
  obtain ⟨w, hw⟩ := residue_surjective (ρ z)
  exact ⟨w, (mem_maximalIdeal_iff_of_residueHom π ρ hρ _).mpr (by rw [map_sub, hρ, hw, sub_self])⟩

theorem map_sub_self_mem_maximalIdeal (hπu : ¬ IsUnit π) (τ : UVCrossingModel W π ≃+* UVCrossingModel W π)
    (hτ : ∀ w, τ (const π w) = const π w) (z : UVCrossingModel W π) :
    τ z - z ∈ maximalIdeal (UVCrossingModel W π) := by
  obtain ⟨w, hw⟩ := exists_sub_const_mem_maximalIdeal π hπu z
  have h1 : τ (z - const π w) ∈ maximalIdeal (UVCrossingModel W π) := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hw ⊢
    exact fun h => hw ((isUnit_map_iff (τ : UVCrossingModel W π →+* UVCrossingModel W π) _).mp
      (by exact h))
  have : τ z - z = τ (z - const π w) - (z - const π w) := by rw [map_sub, hτ]; ring
  rw [this]
  exact sub_mem h1 hw

end Crossing

section Adic
variable {R : Type*} [CommRing R] (I : Ideal R)

theorem not_isUnit_of_of_mem (hI : I ≠ ⊤) {s : R} (hs : s ∈ I) : ¬ IsUnit (AdicCompletion.of I R s) := by
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ I 1)
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [pow_one]), isUnit_zero_iff,
    Ideal.Quotient.zero_eq_one_iff, pow_one] at h1
  exact hI h1

theorem evalₐ_iterate_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z))
    (m n : ℕ) (x : AdicCompletion I R) (z : R) (hz : Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x) :
    AdicCompletion.evalₐ I n (ĝ^[m] x) = Ideal.Quotient.mk (I ^ n) (g^[m] z) := by
  induction m with
  | zero => simpa using hz.symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hĝ n _ _ ih.symm

theorem of_eq_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z)) (s : R) :
    ĝ (AdicCompletion.of I R s) = AdicCompletion.of I R (g s) :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [hĝ n _ s (AdicCompletion.evalₐ_of I n s).symm, AdicCompletion.evalₐ_of]

theorem iterate_eq_self_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z))
    (e : ℕ) (hge : ∀ z, g^[e] z = z) (x : AdicCompletion I R) : ĝ^[e] x = x :=
  AdicCompletion.ext_evalₐ fun n => by
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [evalₐ_iterate_of_levelwise I g ĝ hĝ e n x z hz, hge, hz]

end Adic

section W
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)

theorem isPrecomplete_map_mk {A : Type*} [CommRing A] (I J : Ideal A) [hI : IsPrecomplete I A] :
    IsPrecomplete (I.map (Ideal.Quotient.mk J)) (A ⧸ J) := by
  constructor
  intro f hf

  have hstep : ∀ n, f (n + 1) - f n ∈ (I ^ n).map (Ideal.Quotient.mk J) := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top] at h
    exact h

  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  choose d hd hdq using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).mp (hstep n)
  obtain ⟨g0, hg0⟩ := hsurj (f 0)
  let g : ℕ → A := fun n => Nat.rec g0 (fun k acc => acc + d k) n
  have hg_succ : ∀ n, g (n + 1) = g n + d n := fun n => rfl
  have hgf : ∀ n, Ideal.Quotient.mk J (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hdq]; ring

  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, hg_succ, smul_eq_mul, Ideal.mul_top]
      have : g n - (g n + d n) = -d n := by ring
      rw [this]
      exact Submodule.neg_mem _ (Ideal.pow_le_pow_right hmn (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI hgc
  refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [SModEq.sub_mem, ← hgf, ← map_sub, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_map_of_mem _ h

abbrev IW : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}

theorem W_facts (hϖ : Irreducible ϖ) : (IW ϖ).IsPrime ∧ IsPrincipalIdealRing (PowerSeries O ⧸ IW ϖ) ∧ IsLocalRing (PowerSeries O ⧸ IW ϖ)
    ∧ Irreducible (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) := by
  have h := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ 1 le_rfl
  rw [pow_one] at h
  exact h

end W

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 12800000 in
theorem main (hq : 5 ≤ q) (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [IsNoetherianRing ↥(SL q A red l K)] [IsLocalRing ↥(SL q A red l K)]
    (g : ↥(SL q A red l K) ≃+* ↥(SL q A red l K))
    (hgC : ∀ o : ↥(coeffSubring A K), g (ev q A red l K (MvPolynomial.C o)) = ev q A red l K (MvPolynomial.C o))
    (hge : ∀ z : ↥(SL q A red l K), g^[jWidth a] z = z)
    (ζ₀ ζ₀' : ↥(coeffSubring A K))
    (hζe : redRestrict red K ζ₀ ^ jWidth a = 1)
    (hζprim : ∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1)
    (hζinv : redRestrict red K ζ₀ * redRestrict red K ζ₀' = 1)
    (htanH : g (ev q A red l K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))
          - ev q A red l K (MvPolynomial.C ζ₀) * ev q A red l K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
        ∈ Ideal.span {ev q A red l K (MvPolynomial.C ϖ), ev q A red l K (MvPolynomial.X 0 - MvPolynomial.C y),
            ev q A red l K (MvPolynomial.X 1 - MvPolynomial.C (y ^ q))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(SL q A red l K))})
    (htanG : g (ev q A red l K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q))
          - ev q A red l K (MvPolynomial.C ζ₀') * ev q A red l K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
        ∈ Ideal.span {ev q A red l K (MvPolynomial.C ϖ), ev q A red l K (MvPolynomial.X 0 - MvPolynomial.C y),
            ev q A red l K (MvPolynomial.X 1 - MvPolynomial.C (y ^ q))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(SL q A red l K))})
    (ĝ : AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K) ≃+*
      AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K))
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K)) (z : ↥(SL q A red l K)),
        Ideal.Quotient.mk (maximalIdeal ↥(SL q A red l K) ^ n) z = AdicCompletion.evalₐ (maximalIdeal ↥(SL q A red l K)) n x →
        AdicCompletion.evalₐ (maximalIdeal ↥(SL q A red l K)) n (ĝ x) = Ideal.Quotient.mk (maximalIdeal ↥(SL q A red l K) ^ n) (g z)) :
    ∃ (Φ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) →+*
          AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K))
      (w w' : (AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K))ˣ),
      Function.Injective Φ ∧
      (∀ z, z ∈ Set.range Φ ↔ ĝ z = z) ∧
      (∀ o : ↥(coeffSubring A K), Φ (UVCrossingModel.const _ (Ideal.Quotient.mk _ (PowerSeries.C o))) =
          algebraMap ↥(SL q A red l K) _ (ev q A red l K (MvPolynomial.C o))) ∧
      Φ (UVCrossingModel.U _) = (w : AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K)) *
          (algebraMap ↥(SL q A red l K) _ (ev q A red l K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q))) ^ jWidth a ∧
      Φ (UVCrossingModel.V _) = (w' : AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K)) *
          (algebraMap ↥(SL q A red l K) _ (ev q A red l K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))) ^ jWidth a := by
  classical
  have hq2 : q ≠ 2 := by omega
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := stepA_dvr red K q
  have hϖirr : Irreducible ϖ := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext c
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton,
      isUnit_coeffSubring_iff red K q c, not_not, hϖ c]
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
    · rintro ⟨d, rfl⟩; exact Dvd.intro d rfl
  have hϖ0 : redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

  set e : ℕ := jWidth a with he_def
  have he0 : 0 < e := jWidth_pos a
  have halg : ∀ s : ↥(SL q A red l K), algebraMap ↥(SL q A red l K) (AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K)) s
      = AdicCompletion.of (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K) s := fun s => by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  obtain ⟨θ₂, v₂, ι₂, -, hθC, hιC, hιU, hιV⟩ :=
    ModularCurve.LambdaNodeLocalized.exists_ringEquiv_adicCompletion_lambdaLocalizedAtPoint_uvCrossingModel hq red l hl2
      hl0 hl1 ⟨a, ha, hla⟩ K y hy ϖ hϖ eK ε heK hε hqϖ

  obtain ⟨hprime, hpir, hlocW, hϖW⟩ := W_facts ϖ hϖirr
  haveI := hprime
  haveI : IsDomain (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := Ideal.Quotient.isDomain _
  haveI := hpir
  haveI := hlocW
  haveI : IsDiscreteValuationRing (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    ⟨fun h0 => hϖW.ne_zero (by
      have hmem : (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := hϖW.not_isUnit
      rw [h0] at hmem
      exact hmem)⟩
  have hmaxW : maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) = Ideal.span {(Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ))} := hϖW.maximalIdeal_eq
  have hmkX : Ideal.Quotient.mk (IW ϖ) PowerSeries.X = (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) := by
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hmaxW' : maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)
      = (Ideal.span {PowerSeries.X}).map (Ideal.Quotient.mk (IW ϖ)) := by
    rw [hmaxW, Ideal.map_span, Set.image_singleton, hmkX]
  haveI : IsPrecomplete (maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)) (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := by
    rw [hmaxW']; exact isPrecomplete_map_mk _ _
  haveI : IsAdicComplete (maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)) (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := { }
  have hP1m : (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := hϖW.not_isUnit
  have hπm : (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    Ideal.pow_mem_of_mem _ hP1m _ heK
  have hπu : ¬ IsUnit ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) := (mem_maximalIdeal _).mp hπm
  have hπ0 : (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK ∈ nonZeroDivisors (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖW.ne_zero)
  have hnil : ∃ n : ℕ, maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ^ n ≤ Ideal.span {(Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK} :=
    ⟨eK, by rw [hmaxW, Ideal.span_singleton_pow]⟩

  have hkerIW : ∀ f ∈ IW ϖ, ((redRestrict red K).comp PowerSeries.constantCoeff) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [RingHom.comp_apply, map_mul, map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub,
      map_mul, map_neg, hϖ0, neg_zero, mul_zero]
  set redW : (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) →+* k := Ideal.Quotient.lift (IW ϖ) _ hkerIW with hredWdef
  have hredC : ∀ o, redW (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C o)) = redRestrict red K o := fun o => by
    rw [hredWdef, Ideal.Quotient.lift_mk, RingHom.comp_apply, PowerSeries.constantCoeff_C]
  have hredP1 : redW (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) = 0 := by rw [hredC, hϖ0]
  have hkerW : ∀ w, w ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ↔ redW w = 0 := by
    intro w
    constructor
    · intro hw
      rw [hmaxW, Ideal.mem_span_singleton'] at hw
      obtain ⟨c, rfl⟩ := hw
      rw [map_mul, hredP1, mul_zero]
    · intro hw
      by_contra hw'
      have hu : IsUnit w := by rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at hw'
      exact not_isUnit_zero (hw ▸ hu.map redW)
  have hunitW : ∀ w, redW w ≠ 0 → IsUnit w := fun w hw => by
    by_contra h
    exact hw ((hkerW w).mp ((mem_maximalIdeal w).mpr h))

  have hq6 : ¬ q ∣ 6 := by
    intro h
    have h6 : q ≤ 6 := Nat.le_of_dvd (by norm_num) h
    have hp : q.Prime := Fact.out
    interval_cases q
    · exact absurd h (by decide)
    · exact absurd hp (by norm_num)
  have hek : (e : k) ≠ 0 := by
    obtain ⟨c, hc⟩ := jWidth_dvd_six a
    intro h
    apply hq6
    refine (CharP.cast_eq_zero_iff k q 6).mp ?_
    rw [hc, Nat.cast_mul, ← he_def, h, zero_mul]
  have heW : IsUnit ((e : ℕ) : PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    hunitW _ (by rwa [map_natCast])

  have hrZ0 : redW (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀)) = redRestrict red K ζ₀ := hredC ζ₀
  have hrZ0p : redW (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) = redRestrict red K ζ₀' := hredC ζ₀'
  have hrζ0 : redRestrict red K ζ₀ ≠ 0 := left_ne_zero_of_mul_eq_one hζinv
  haveI : HenselianRing (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) (maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)) :=
    IsAdicComplete.henselianRing _ _
  obtain ⟨ζ, hζroot, hζZ0⟩ := HenselianRing.is_henselian (I := maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ))
    (Polynomial.X ^ e - Polynomial.C 1) (Polynomial.monic_X_pow_sub_C 1 he0.ne') (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀))
    (by
      rw [hkerW, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, map_sub, map_pow,
        map_one, hrZ0, hζe, sub_self])
    (by
      refine (hunitW _ ?_).map _
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_natCast, map_pow, hrZ0]
      exact mul_ne_zero hek (pow_ne_zero _ hrζ0))
  have hζe' : ζ ^ e = 1 := by
    have h := hζroot
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h
    exact h
  have hredζ : redW ζ = redRestrict red K ζ₀ := by
    have h := (hkerW _).mp hζZ0
    rw [map_sub, sub_eq_zero] at h
    rw [h, hrZ0]
  have hζζ' : ζ * ζ ^ (e - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel he0, hζe']
  have hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := by
    intro m hm0 hme
    refine mem_nonZeroDivisors_of_ne_zero fun h => hζprim m hm0 hme ?_
    have h' := congrArg redW h
    rw [map_sub, map_pow, map_one, map_zero, hredζ, sub_eq_zero] at h'
    exact h'
  have hζpZ0p : ζ ^ (e - 1) - (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := by
    rw [hkerW, map_sub, map_pow, hredζ, hrZ0p, sub_eq_zero]
    refine mul_left_cancel₀ hrζ0 ?_
    rw [hζinv, ← pow_succ', Nat.sub_add_cancel he0, hζe]

  haveI hMloc : IsLocalRing (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) :=
    ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu
  haveI hMcomp := ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal (Ô := PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)
  have hUm := U_mem_maximalIdeal ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) hπu
  have hVm := V_mem_maximalIdeal ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) hπu

  have hconst : ∀ o : ↥(coeffSubring A K), ι₂ (algebraMap _ _ (ev q A red l K (MvPolynomial.C o)))
      = UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C o)) := fun o => by
    rw [← hθC o, hιC]

  set σ₀ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ≃+*
      UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) := (ι₂.symm.trans ĝ).trans ι₂ with hσ₀def
  have hσ₀ : ∀ z, σ₀ z = ι₂ (ĝ (ι₂.symm z)) := fun z => rfl
  have hĝof : ∀ s : ↥(SL q A red l K), ĝ (algebraMap _ _ s) = algebraMap _ _ (g s) := fun s => by
    rw [halg, halg]; exact of_eq_of_levelwise _ g ĝ hĝ s
  have hσ₀ψ : ∀ s : ↥(SL q A red l K), σ₀ (ι₂ (algebraMap _ _ s)) = ι₂ (algebraMap _ _ (g s)) := fun s => by
    rw [hσ₀, RingEquiv.symm_apply_apply, hĝof]
  have hσ₀C : ∀ o : ↥(coeffSubring A K), σ₀ (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C o)))
      = UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C o)) := fun o => by
    rw [← hconst, hσ₀ψ, hgC]
  have hσ₀π : σ₀ (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ))) = UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) := hσ₀C ϖ

  have hσ₀W : ∀ w, σ₀ (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) w) = UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) w := by
    have key : σ₀.toRingHom.comp (UVCrossingModel.constHom ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) = UVCrossingModel.constHom ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) := by
      refine ringHom_ext_of_isHausdorff (IW ϖ) (T := UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))
        (maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))) _ _
        (fun o => ?_) ?_ ?_
      · exact hσ₀C o
      · show σ₀ (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) _) = UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) _
        rw [hmkX, hσ₀π]
      · show σ₀ (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) _) ∈ _
        rw [hmkX, hσ₀π, const_mem_maximalIdeal_iff _ hπu]
        exact hP1m
    intro w
    exact congrArg (fun ψ => ψ w) key
  set σ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ≃ₐ[PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ]
      UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) := AlgEquiv.ofRingEquiv (f := σ₀)
        (fun w => by show σ₀ (UVCrossingModel.const _ w) = UVCrossingModel.const _ w; exact hσ₀W w) with hσdef
  have hσ : ∀ z, σ z = σ₀ z := fun _ => rfl

  have hsemi : Function.Semiconj ι₂ ĝ σ := fun x => by
    rw [hσ, hσ₀, RingEquiv.symm_apply_apply]
  have hord : ∀ z, σ^[e] z = z := by
    intro z
    have h := hsemi.iterate_right e (ι₂.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    rw [← h, iterate_eq_self_of_levelwise _ g ĝ hĝ e hge, RingEquiv.apply_symm_apply]

  have hmS : maximalIdeal ↥(SL q A red l K) = Ideal.span {ev q A red l K (MvPolynomial.C ϖ),
      ev q A red l K (MvPolynomial.X 0 - MvPolynomial.C y), ev q A red l K (MvPolynomial.X 1 - MvPolynomial.C (y ^ q))} :=
    (ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring hq2 red l hl2 K y hy
      ϖ hϖ).2.2.2
  set ψ : ↥(SL q A red l K) →+* UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) :=
    ι₂.toRingHom.comp (algebraMap _ _) with hψdef
  have hψ : ∀ s, ψ s = ι₂ (algebraMap _ _ s) := fun _ => rfl
  have hψm : maximalIdeal ↥(SL q A red l K) ≤ Ideal.comap ψ (maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))) := by
    intro s hs
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, hψ, halg]
    intro hu
    have hu' : IsUnit (AdicCompletion.of (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K) s) := by
      simpa using hu.map ι₂.symm
    exact not_isUnit_of_of_mem _ (maximalIdeal.isMaximal _).ne_top hs hu'
  have hqM : ((q : ℕ) : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ∈
      maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
    have hqW : ((q : ℕ) : PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) = (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK * Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ε) := by
      rw [← map_natCast ((Ideal.Quotient.mk (IW ϖ)).comp PowerSeries.C) q, hqϖ, map_mul, map_pow]
      rfl
    have h1 : ((q : ℕ) : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) =
        UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) *
          UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ε)) := by
      rw [ModularCurve.UVCrossingModel.U_mul_V, ← map_natCast (UVCrossingModel.constHom ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) q, hqW, map_mul,
        UVCrossingModel.constHom_apply, UVCrossingModel.constHom_apply]
    rw [h1, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hUm hVm)

  have htrans : ∀ s : ↥(SL q A red l K), s ∈ Ideal.span {ev q A red l K (MvPolynomial.C ϖ),
      ev q A red l K (MvPolynomial.X 0 - MvPolynomial.C y), ev q A red l K (MvPolynomial.X 1 - MvPolynomial.C (y ^ q))} ^ 2
        ⊔ Ideal.span {((q : ℕ) : ↥(SL q A red l K))} →
      ψ s ∈ maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
    intro s hs
    have hle : Ideal.span {ev q A red l K (MvPolynomial.C ϖ),
      ev q A red l K (MvPolynomial.X 0 - MvPolynomial.C y), ev q A red l K (MvPolynomial.X 1 - MvPolynomial.C (y ^ q))} ^ 2
        ⊔ Ideal.span {((q : ℕ) : ↥(SL q A red l K))} ≤ Ideal.comap ψ (maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2) := by
      refine sup_le ?_ ?_
      · rw [← hmS]
        exact (Ideal.pow_right_mono hψm 2).trans (Ideal.le_comap_pow _ 2)
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact hqM
    exact hle hs
  have hconst_mem : ∀ w, w ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) →
      UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) w ∈ maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) :=
    fun w hw => (const_mem_maximalIdeal_iff _ hπu w).mpr hw

  have htanV : σ (UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ζ * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ∈
      maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
    have h1 := htrans _ htanH
    rw [map_sub ψ, map_mul ψ, hψ, hψ, hψ, ← hσ₀ψ, hιV, hconst] at h1
    have h2 : (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ζ - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀))) * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ∈
        maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
      rw [← const_sub', pow_two]; exact Ideal.mul_mem_mul (hconst_mem _ hζZ0) hVm
    have : σ (UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ζ * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)
        = (σ₀ (UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀)) * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))
          + (-1) * ((UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ζ - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀))) * UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) := by
      rw [hσ]; ring
    rw [this]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ h2)

  have htanU : σ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (ζ ^ (e - 1)) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ∈
      maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
    have h1 := htrans _ htanG
    rw [map_sub ψ, map_mul ψ, hψ, hψ, hψ, ← hσ₀ψ, hιU, hconst, map_mul σ₀] at h1

    set v' := ι₂ (v₂ : AdicCompletion (maximalIdeal ↥(SL q A red l K)) ↥(SL q A red l K)) with hv'def
    have hv'u : IsUnit v' := (Units.isUnit v₂).map ι₂
    have hd : σ₀ v' - v' ∈ maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) :=
      map_sub_self_mem_maximalIdeal _ hπu σ₀ hσ₀W v'
    have hσU : σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ∈ maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) := by
      have := map_sub_self_mem_maximalIdeal _ hπu σ₀ hσ₀W (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))
      simpa using add_mem this hUm
    have h2 : (σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * v' ∈
        maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
      have h3 : σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * (σ₀ v' - v') ∈
          maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hσU hd
      have : (σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * v'
          = (σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * σ₀ v' - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) * (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) * v'))
            + (-1) * (σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * (σ₀ v' - v')) := by ring
      rw [this]
      exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ h3)
    have h4 : σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ∈
        maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
      obtain ⟨u, hu⟩ := hv'u
      have := Ideal.mul_mem_right (↑u⁻¹ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) _ h2
      rwa [← hu, mul_assoc, Units.mul_inv, mul_one] at this
    have h5 : (UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (ζ ^ (e - 1)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀'))) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ∈
        maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) ^ 2 := by
      rw [← const_sub', pow_two]; exact Ideal.mul_mem_mul (hconst_mem _ hζpZ0p) hUm
    have : σ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (ζ ^ (e - 1)) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)
        = (σ₀ (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀')) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK))
          + (-1) * ((UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (ζ ^ (e - 1)) - UVCrossingModel.const ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ζ₀'))) * UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) := by
      rw [hσ]; ring
    rw [this]
    exact Ideal.add_mem _ h4 (Ideal.mul_mem_left _ _ h5)

  have hξζ : ζ ^ (e - 1) * ζ = 1 := by rw [mul_comm, hζζ']
  have hξe : (ζ ^ (e - 1)) ^ e = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζe', one_pow]
  have hregξ : ∀ m : ℕ, 0 < m → m < e → (ζ ^ (e - 1)) ^ m - 1 ∈ nonZeroDivisors (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := by
    intro m hm0 hme
    refine mem_nonZeroDivisors_of_ne_zero fun h => hζprim m hm0 hme ?_
    have h' : (ζ ^ (e - 1)) ^ m = 1 := sub_eq_zero.mp h
    have hm1 : ζ ^ m = 1 := by
      calc ζ ^ m = ζ ^ m * (ζ ^ (e - 1)) ^ m := by rw [h', mul_one]
        _ = (ζ * ζ ^ (e - 1)) ^ m := (mul_pow _ _ _).symm
        _ = 1 := by rw [hζζ', one_pow]
    have h'' := congrArg redW hm1
    rwa [map_pow, map_one, hredζ] at h''
  have key := ModularCurve.UVCrossingModel.exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
    ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) hπu hπ0 hnil e heW (ζ ^ (e - 1)) ζ hξζ hξe hregξ σ hord htanU htanV
  have hpow : ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK) ^ e = (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ (jWidth a * eK) := by rw [← pow_mul, mul_comm]
  rw [hpow] at key
  obtain ⟨ι₃, γ, hinj, hfix, -, hι₃U, hι₃V⟩ := key

  have hι₂U : ι₂.symm (UVCrossingModel.U ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) =
      algebraMap _ _ (ev q A red l K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)) * ↑(v₂⁻¹) := by
    have h := congrArg ι₂.symm hιU
    rw [map_mul ι₂.symm, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply] at h
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hι₂V : ι₂.symm (UVCrossingModel.V ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) = algebraMap _ _ (ev q A red l K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) := by
    apply ι₂.injective
    rw [RingEquiv.apply_symm_apply, hιV]
  have hwu : IsUnit ((ι₂.symm (γ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)) * ↑(v₂⁻¹)) ^ e) :=
    (((Units.isUnit γ).map ι₂.symm).mul (Units.isUnit _)).pow e
  have hw'u : IsUnit ((ι₂.symm ((↑γ⁻¹ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) ((Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) ^ eK)))) ^ e) :=
    ((Units.isUnit _).map ι₂.symm).pow e
  refine ⟨ι₂.symm.toRingHom.comp ι₃.toRingHom, hwu.unit, hw'u.unit, ι₂.symm.injective.comp hinj, fun z => ?_, fun o => ?_, ?_, ?_⟩
  ·
    constructor
    · rintro ⟨m, rfl⟩
      show ĝ (ι₂.symm (ι₃ m)) = ι₂.symm (ι₃ m)
      apply ι₂.injective
      have h := (hfix (ι₃ m)).mpr ⟨m, rfl⟩
      rw [hσ, hσ₀] at h
      rw [h, RingEquiv.apply_symm_apply]
    · intro hz
      have h : σ (ι₂ z) = ι₂ z := by rw [hσ, hσ₀, RingEquiv.symm_apply_apply, hz]
      obtain ⟨m, hm⟩ := (hfix (ι₂ z)).mp h
      exact ⟨m, by show ι₂.symm (ι₃ m) = z; rw [hm, RingEquiv.symm_apply_apply]⟩
  ·
    show ι₂.symm (ι₃ (UVCrossingModel.const _ _)) = _
    rw [const_eq_algebraMap', AlgHom.commutes, ← const_eq_algebraMap', ← hconst, RingEquiv.symm_apply_apply]
  · show ι₂.symm (ι₃ (UVCrossingModel.U _)) = _
    rw [hι₃U, map_pow ι₂.symm, map_mul ι₂.symm, hι₂U, IsUnit.unit_spec, ← mul_pow]
    congr 1
    ring
  · show ι₂.symm (ι₃ (UVCrossingModel.V _)) = _
    rw [hι₃V, map_pow ι₂.symm, map_mul ι₂.symm, hι₂V, IsUnit.unit_spec, ← mul_pow]

end Main

end Ws30FixSigma
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion.ModularCurve ModularCurve.Ws30FixSigma in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]

    (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hgC : ∀ o : ↥(coeffSubring A K), g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
    (hge : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), g^[jWidth a] z = z)

    (ζ₀ ζ₀' : ↥(coeffSubring A K))
    (hζe : redRestrict red K ζ₀ ^ jWidth a = 1)
    (hζprim : ∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1)
    (hζinv : redRestrict red K ζ₀ * redRestrict red K ζ₀' = 1)

    (htanH : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})
    (htanG : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})

    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) z = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n x →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n (ĝ x) = Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) (g z)) :
    ∃ (Φ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
      (w w' : (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))ˣ),
      Function.Injective Φ ∧
      (∀ z : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), z ∈ Set.range Φ ↔ ĝ z = z) ∧
      (∀ o : ↥(coeffSubring A K), Φ (UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) (Ideal.Quotient.mk _ (PowerSeries.C o)))
          = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ∧
      Φ (UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a ∧
      Φ (UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w' : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a :=
  ModularCurve.Ws30FixSigma.main hq red a ha h01728 l hl2 hl0 hl1 hla K y hy ϖ hϖ eK ε heK hε hqϖ g hgC hge ζ₀ ζ₀' hζe hζprim hζinv htanH htanG ĝ hĝ

end S_ModularCurve_LambdaNodeLocalized_exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringHom_uvCrossingModel_pow_jWidth_range_eq_fixedPoints_adicCompletion (solution)
