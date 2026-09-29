-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_level_two_value_sub_const_mem_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4dc8a640-fd6c-57ad-a334-942288be45b3

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_level_two_value_sub_const_mem_of_isMaximal
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_level_two_value_sub_const_mem_of_isMaximal.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC evalAtLambdaInt evalAtLambdaInt_X laurentMap laurentMap_qExpand laurentMap_laurentMap reduceModBivar ssJSet LambdaModularPolynomialData LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing exists_lambdaKroneckerCongruence"
p2m_open "ModularCurve"
namespace Ws35ORB

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

section Integral
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] [CharP k q]
  (K : IntermediateField ℚ Qb)

theorem inv_two_pow_mem (red : A →+* k) (hq : 5 ≤ q) (n : ℕ) : ((2 : Qb) ^ n)⁻¹ ∈ coeffSubring A K := by
  have h : IsUnit (((2 ^ n : ℕ) : ↥(coeffSubring A K))) := by
    rw [isUnit_coeffSubring_iff red K q, map_natCast, Ne, CharP.cast_eq_zero_iff k q]
    intro hdvd
    have h2 : q ∣ 2 := (Fact.out : q.Prime).dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨u, hu⟩ := h
  have hmul : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * (2 : Qb) ^ n = 1 := by
    have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) u.inv_mul
    rw [hu] at h1
    first
      | simpa using h1
      | (have h' := h1; simp at h'; exact h')
      | (simp; exact h1)
      | exact h1
  have : ((2 : Qb) ^ n)⁻¹ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [this]; exact SetLike.coe_mem _

omit [CharP k q] in
theorem ev_C_coe (red : A →+* k) (a : k) (c : ↥(coeffSubring A K)) :
    ((ev q A red a K (MvPolynomial.C c) : ↥(R₀ q A red a K)) : LQ) = algebraMap Qb LQ (c : Qb) := by
  show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) = _
  rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl

theorem isIntegralElem_sixteen_mul (red : A →+* k) (a : k) (hq : 5 ≤ q)
    (J : ↥(R₀ q A red a K)) (m : LQ)
    (hJ : qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) :
    ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (16 * m) := by
  set f := (qExpand Qb 2).comp (R₀ q A red a K).subtype with hf
  have h256mem : (256 : Qb)⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 8; norm_num at this; rwa [one_div] at this
  let c : ↥(R₀ q A red a K) := ev q A red a K (MvPolynomial.C ⟨(256 : Qb)⁻¹, h256mem⟩) * J
  have hc : f c = algebraMap Qb LQ (256 : Qb)⁻¹ * qExpand Qb 2 (J : LQ) := by
    rw [hf, RingHom.comp_apply, Subring.subtype_apply, Subring.coe_mul, map_mul, ev_C_coe, qExpand_algebraMap]
  have h256 : algebraMap Qb LQ (256 : Qb)⁻¹ * 256 = 1 := by
    rw [← map_ofNat (algebraMap Qb LQ) 256, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  open Polynomial in
  refine ⟨(X ^ 2 - X + 1) ^ 3 - C c * (X ^ 2 * (X - 1) ^ 2), by monicity!, ?_⟩
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one, hc]
  linear_combination (-1 : LQ) * hJ - (qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2) * h256

theorem isIntegralElem_of_jRel (red : A →+* k) (a : k) (hq : 5 ≤ q)
    (J : ↥(R₀ q A red a K)) (m : LQ)
    (hJ : qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) :
    ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem m := by
  have h16mem : (16 : Qb)⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 4; norm_num at this; rwa [one_div] at this
  refine RingHom.IsIntegralElem.of_mul_unit _ m 16 (ev q A red a K (MvPolynomial.C ⟨(16 : Qb)⁻¹, h16mem⟩)) ?_ ?_
  · rw [RingHom.comp_apply, Subring.subtype_apply, ev_C_coe, qExpand_algebraMap,
      ← map_ofNat (algebraMap Qb LQ) 16, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  · rw [mul_comm]; exact isIntegralElem_sixteen_mul q A K red a hq J m hJ

end Integral

section Roots

theorem level_two_root_cases
    {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (l' : k) (hla' : a * ((16 * l') ^ 2 * (16 * l' - 1) ^ 2) = 256 * ((16 * l') ^ 2 - 16 * l' + 1) ^ 3) :
    (a = 0 ∧ (l' = l ∨ l' = 16⁻¹ - l)) ∨ (a = 1728 ∧ (l' = -16⁻¹ ∨ l' = 8⁻¹ ∨ l' = 32⁻¹)) := by
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
  · left
    refine ⟨rfl, ?_⟩
    have hQ : ∀ t : k, 0 * ((16 * t) ^ 2 * (16 * t - 1) ^ 2) = 256 * ((16 * t) ^ 2 - 16 * t + 1) ^ 3 →
        (16 * t) ^ 2 - 16 * t + 1 = 0 := by
      intro t ht
      rw [zero_mul] at ht
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp ht.symm).resolve_left h256)
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
  · right
    refine ⟨rfl, ?_⟩
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

end Roots

section PsiT
variable {q : ℕ} [Fact q.Prime] {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L)
  (data : LambdaModularPolynomialData q)

def psiT : MvPolynomial (Fin 2) A :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
    (MvPolynomial.X 1) data.Ψ

theorem lambdaEval_psiT : lambdaEval q A (psiT A data) = 0 := by
  set mE := lambdaEval q A with hmE
  set θ : Polynomial ℤ →+* LaurentSeries L := Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L) with hθ
  have hgen0 : mE (MvPolynomial.X 0) = lambdaModC L := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  have hgen1 : mE (MvPolynomial.X 1) = lambdaNModC L q := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  have hLHS : mE (psiT A data) = data.Ψ.eval₂ θ (lambdaNModC L q) := by
    rw [psiT, Polynomial.hom_eval₂, hgen1]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hθ,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hθ,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgen0]
  set E : LaurentSeries ℚ →+* LaurentSeries L := laurentMap (algebraMap ℚ L) with hE
  have hZ : (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L := RingHom.ext_int _ _
  have hE1 : E (lambdaNModC ℚ q) = lambdaNModC L q := by
    rw [hE, lambdaNModC, laurentMap_qExpand, lambdaNModC, lambdaModC, lambdaModC, laurentMap_laurentMap, hZ]
  have hEθ : E.comp ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) = θ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast, evalAtLambdaInt]
    · rw [RingHom.coe_comp, Function.comp_apply, RingHom.coe_comp, Function.comp_apply, evalAtLambdaInt_X, hE,
        laurentMap_laurentMap, hZ, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, lambdaModC]
  have hΨ : data.Ψ.eval₂ θ (lambdaNModC L q) = 0 := by
    have h := congrArg E data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂, hEθ, hE1] at h
    exact h
  rw [hLHS, hΨ]

end PsiT

section NonUnits
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

theorem ev_mem_maximalIdeal_of_pointEval_eq_zero [IsLocalRing ↥(R₀ q A red a K)]
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hp : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p = 0) :
    ev q A red a K p ∈ IsLocalRing.maximalIdeal ↥(R₀ q A red a K) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨r, s, hs, hws⟩ := w.2

  have h1 : modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) (p * r) := by
    have hw' : ((ev q A red a K p : ↥(R₀ q A red a K)) : LQ) * (w : LQ) = 1 := by
      have := congrArg (fun z : ↥(R₀ q A red a K) => (z : LQ)) hw
      simpa using this
    have h := congrArg (fun z : LQ => ((ev q A red a K p : ↥(R₀ q A red a K)) : LQ) * z) hws
    simp only at h
    rw [← mul_assoc, hw'] at h
    rw [show (1 : LQ) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) s
      from one_mul _] at h
    rw [h, map_mul]
  have h2 : modularEval (1 * q) (coeffSubring A K) (s - p * r) = 0 := by rw [map_sub, h1, sub_self]
  have h3 := ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K _ h2
  rw [map_sub, map_mul, hp, zero_mul, sub_zero] at h3
  exact hs h3

end NonUnits

end Ws35ORB
end ModularCurve

open ModularCurve.Ws35ORB in
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
    (Q : Ideal ↥B) (hQ : Q.IsMaximal) :
    ∃ (l' : k) (_ : a * ((16 * l') ^ 2 * (16 * l' - 1) ^ 2) = 256 * ((16 * l') ^ 2 - 16 * l' + 1) ^ 3)
      (y' : ↥(coeffSubring A K)) (_ : redRestrict red K y' = l'),
      (∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ) → b ∈ Q) ∧
      (∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y') → b ∈ Q) ∧
      (∀ b : ↥B, (b : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y' ^ q)) → b ∈ Q) := by
  classical
  have hqP : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k q 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h3k : (3 : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k q 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h16k : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2k
  have h256k : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2k
  have h1728k : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2k) (pow_ne_zero _ h3k)

  have hl2 : l ^ (q ^ 2) = l := pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l hla
  have hSfacts := ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
    hq2 red l hl2 K y hy ϖ hϖ
  haveI : IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := hSfacts.2.1
  obtain ⟨hRB, hTB, -⟩ :=
    ModularCurve.LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem hq red a ha ha2 h01728 K
      l hla y hy B hB

  let evB : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥B := (lambdaEval q (coeffSubring A K)).codRestrict B hTB
  have evB_coe : ∀ p, ((evB p : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaEval q (coeffSubring A K) p := fun _ => rfl
  let cB : ↥(coeffSubring A K) →+* ↥B := evB.comp MvPolynomial.C
  have cB_coe : ∀ c : ↥(coeffSubring A K), ((cB c : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : (AlgebraicClosure ℚ)) := by
    intro c
    show lambdaEval q (coeffSubring A K) (MvPolynomial.C c) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl
  haveI : Q.IsMaximal := hQ
  letI : Field (↥B ⧸ Q) := Ideal.Quotient.field Q
  let π : ↥B →+* ↥B ⧸ Q := Ideal.Quotient.mk Q
  let redκ : ↥(coeffSubring A K) →+* ↥B ⧸ Q := π.comp cB

  letI algRB : Algebra ↥(R₀ q A red a K) ↥B :=
    (((qExpand (AlgebraicClosure ℚ) 2).comp (R₀ q A red a K).subtype).codRestrict B (fun z => hRB z z.2)).toAlgebra
  have algRB_coe : ∀ r : ↥(R₀ q A red a K), ((algebraMap ↥(R₀ q A red a K) ↥B r : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (r : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun _ => rfl
  haveI : Algebra.IsIntegral ↥(R₀ q A red a K) ↥B := by
    refine ⟨fun b => ?_⟩
    obtain ⟨-, p, hpm, hpb⟩ := (hB (b : LaurentSeries (AlgebraicClosure ℚ))).mp b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ p (algebraMap ↥(R₀ q A red a K) ↥B) B.subtype b
    have hcomp : B.subtype.comp (algebraMap ↥(R₀ q A red a K) ↥B) = (qExpand (AlgebraicClosure ℚ) 2).comp (R₀ q A red a K).subtype :=
      RingHom.ext fun _ => rfl
    rw [hcomp] at h
    show B.subtype (Polynomial.eval₂ (algebraMap ↥(R₀ q A red a K) ↥B) b p) = B.subtype 0
    rw [h, map_zero]
    exact hpb
  have hcomap : Q.comap (algebraMap ↥(R₀ q A red a K) ↥B) = IsLocalRing.maximalIdeal ↥(R₀ q A red a K) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
  have hmaxQ : ∀ r ∈ IsLocalRing.maximalIdeal ↥(R₀ q A red a K), algebraMap ↥(R₀ q A red a K) ↥B r ∈ Q := by
    intro r hr
    rw [← hcomap] at hr
    exact hr

  have alg_evC : ∀ c : ↥(coeffSubring A K), algebraMap ↥(R₀ q A red a K) ↥B (ev q A red a K (MvPolynomial.C c)) = cB c := by
    intro c
    apply Subtype.ext
    rw [algRB_coe, ev_C_coe, qExpand_algebraMap, cB_coe]

  have hredϖ : redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, by ring⟩
  have hcQ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 → cB c ∈ Q := by
    intro c hc
    rw [← alg_evC]
    refine hmaxQ _ (ev_mem_maximalIdeal_of_pointEval_eq_zero q A red a K _ ?_)
    rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact hc
  have hϖQ : cB ϖ ∈ Q := hcQ ϖ hredϖ
  have hredκ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 → redκ c = 0 := fun c hc =>
    (Ideal.Quotient.eq_zero_iff_mem.mpr (hcQ c hc))

  have hqκ : ((q : ℕ) : ↥B ⧸ Q) = 0 := by
    have := hredκ (q : ℕ) (by rw [map_natCast, CharP.cast_eq_zero])
    rwa [map_natCast] at this
  haveI : CharP (↥B ⧸ Q) q := (CharP.charP_iff_prime_eq_zero hqP).mpr hqκ

  have h16mem : (16 : (AlgebraicClosure ℚ))⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 4; norm_num at this; rwa [one_div] at this
  let den : ↥(coeffSubring A K) := (16 * y) ^ 2 * (16 * y - 1) ^ 2
  let num : ↥(coeffSubring A K) := 256 * ((16 * y) ^ 2 - 16 * y + 1) ^ 3
  have hden_red : redRestrict red K den = (16 * l) ^ 2 * (16 * l - 1) ^ 2 := by
    simp only [den, map_mul, map_pow, map_sub, map_one, map_ofNat, hy]
  have hnum_red : redRestrict red K num = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 := by
    simp only [num, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hy]
  have hden0 : redRestrict red K den ≠ 0 := by
    rw [hden_red]
    intro h0
    have hn : (256 : k) * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 = 0 := by rw [← hla, h0, mul_zero]
    have hq0 : (16 * l) ^ 2 - 16 * l + 1 = 0 :=
      pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp hn).resolve_left h256k)
    rcases mul_eq_zero.mp h0 with h | h
    · have : 16 * l = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      rw [this] at hq0; norm_num at hq0
    · have : 16 * l - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      have h1 : 16 * l = 1 := sub_eq_zero.mp this
      rw [h1] at hq0; norm_num at hq0
  have hdenu : IsUnit den := (isUnit_coeffSubring_iff red K q den).mpr hden0
  obtain ⟨u, hu⟩ := hdenu.exists_right_inv
  let x : ↥(coeffSubring A K) := num * u
  have hredu : redRestrict red K den * redRestrict red K u = 1 := by rw [← map_mul, hu, map_one]
  have hx : redRestrict red K x = a := by
    show redRestrict red K (num * u) = a
    rw [map_mul, hnum_red, ← hla, ← hden_red, mul_assoc, hredu, mul_one]

  have ev_sub : ∀ p r : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      ev q A red a K p - ev q A red a K r = ev q A red a K (p - r) := fun p r =>
    Subtype.ext (by show modularEval (1 * q) (coeffSubring A K) p - modularEval (1 * q) (coeffSubring A K) r = modularEval (1 * q) (coeffSubring A K) (p - r); rw [map_sub])
  have hjQ : algebraMap ↥(R₀ q A red a K) ↥B (ev q A red a K (MvPolynomial.X 0)) - cB x ∈ Q := by
    rw [← alg_evC, ← map_sub, ev_sub]
    refine hmaxQ _ (ev_mem_maximalIdeal_of_pointEval_eq_zero q A red a K _ ?_)
    rw [map_sub, pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, hx]
    show a - a = 0
    exact sub_self a
  have hjqQ : algebraMap ↥(R₀ q A red a K) ↥B (ev q A red a K (MvPolynomial.X 1)) - cB (x ^ q) ∈ Q := by
    rw [← alg_evC, ← map_sub, ev_sub]
    refine hmaxQ _ (ev_mem_maximalIdeal_of_pointEval_eq_zero q A red a K _ ?_)
    rw [map_sub, pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, map_pow, hx]
    show a ^ q - a ^ q = 0
    exact sub_self _

  let μB : ↥B := evB (MvPolynomial.X 0)
  let μqB : ↥B := evB (MvPolynomial.X 1)
  have μB_coe : ((μB : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) := by
    show lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have μqB_coe : ((μqB : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q := by
    show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  let JB : ↥B := algebraMap ↥(R₀ q A red a K) ↥B (ev q A red a K (MvPolynomial.X 0))
  let JqB : ↥B := algebraMap ↥(R₀ q A red a K) ↥B (ev q A red a K (MvPolynomial.X 1))
  have hev0 : ((ev q A red a K (MvPolynomial.X 0) : ↥(R₀ q A red a K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hev1 : ((ev q A red a K (MvPolynomial.X 1) : ↥(R₀ q A red a K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have JB_coe : ((JB : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)) := by
    rw [algRB_coe, hev0]
  have JqB_coe : ((JqB : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)) := by
    rw [algRB_coe, hev1]
  have hnatB : ∀ n : ℕ, (((n : ↥B)) : LaurentSeries (AlgebraicClosure ℚ)) = n := fun n => rfl
  have h16c : ((16 : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = 16 := hnatB 16
  have h256c : ((256 : ↥B) : LaurentSeries (AlgebraicClosure ℚ)) = 256 := hnatB 256
  have hsexB : JB * μB ^ 2 * (16 * μB - 1) ^ 2 = (256 * μB ^ 2 - 16 * μB + 1) ^ 3 := by
    apply Subtype.ext
    have e : ((JB * μB ^ 2 * (16 * μB - 1) ^ 2 : ↥B) : LaurentSeries (AlgebraicClosure ℚ))
        = (JB : LaurentSeries (AlgebraicClosure ℚ)) * (μB : LaurentSeries (AlgebraicClosure ℚ)) ^ 2
            * (16 * (μB : LaurentSeries (AlgebraicClosure ℚ)) - 1) ^ 2 := by push_cast [h16c, h256c]; ring
    have e' : (((256 * μB ^ 2 - 16 * μB + 1) ^ 3 : ↥B) : LaurentSeries (AlgebraicClosure ℚ))
        = (256 * (μB : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 - 16 * (μB : LaurentSeries (AlgebraicClosure ℚ)) + 1) ^ 3 := by
      push_cast [h16c, h256c]; ring
    rw [e, e', μB_coe, JB_coe]
    exact jLambda_Qb
  have hsexqB : JqB * μqB ^ 2 * (16 * μqB - 1) ^ 2 = (256 * μqB ^ 2 - 16 * μqB + 1) ^ 3 := by
    apply Subtype.ext
    have e : ((JqB * μqB ^ 2 * (16 * μqB - 1) ^ 2 : ↥B) : LaurentSeries (AlgebraicClosure ℚ))
        = (JqB : LaurentSeries (AlgebraicClosure ℚ)) * (μqB : LaurentSeries (AlgebraicClosure ℚ)) ^ 2
            * (16 * (μqB : LaurentSeries (AlgebraicClosure ℚ)) - 1) ^ 2 := by push_cast [h16c, h256c]; ring
    have e' : (((256 * μqB ^ 2 - 16 * μqB + 1) ^ 3 : ↥B) : LaurentSeries (AlgebraicClosure ℚ))
        = (256 * (μqB : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 - 16 * (μqB : LaurentSeries (AlgebraicClosure ℚ)) + 1) ^ 3 := by
      push_cast [h16c, h256c]; ring
    rw [e, e', μqB_coe, JqB_coe]
    exact jLambda_Qb_q (q := q)

  obtain ⟨xκ, hxκ⟩ : ∃ z : ↥B ⧸ Q, z = redκ x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ z : ↥B ⧸ Q, z = π μB := ⟨_, rfl⟩
  obtain ⟨mq, hmq⟩ : ∃ z : ↥B ⧸ Q, z = π μqB := ⟨_, rfl⟩
  have hJκ : π JB = xκ := by
    rw [hxκ, show redκ x = π (cB x) from rfl, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hjQ
  have hJqκ : π JqB = xκ ^ q := by
    rw [hxκ, show redκ x = π (cB x) from rfl, ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hjqQ
  have hsexκ : xκ * ((16 * m) ^ 2 * (16 * m - 1) ^ 2) = 256 * ((16 * m) ^ 2 - 16 * m + 1) ^ 3 := by
    have h := congrArg π hsexB
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hJκ] at h
    rw [← hm] at h
    linear_combination (256 : ↥B ⧸ Q) * h

  have h01728κ : xκ = 0 ∨ xκ = 1728 := by
    rw [hxκ]
    rcases h01728 with h0 | h17
    · left
      exact hredκ x (by rw [hx, h0])
    · right
      have := hredκ (x - 1728) (by rw [map_sub, hx, h17, map_ofNat, sub_self])
      rw [map_sub, map_ofNat, sub_eq_zero] at this
      exact this
  have hxq : xκ ^ q = xκ := by
    rcases h01728κ with h | h
    · rw [h, zero_pow hqP.ne_zero]
    · rw [h]
      have := map_natCast (frobenius (↥B ⧸ Q) q) 1728
      rw [frobenius_def] at this
      exact_mod_cast this
  have hsexqκ : xκ * ((16 * mq) ^ 2 * (16 * mq - 1) ^ 2) = 256 * ((16 * mq) ^ 2 - 16 * mq + 1) ^ 3 := by
    have h := congrArg π hsexqB
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hJqκ, hxq] at h
    rw [← hmq] at h
    linear_combination (256 : ↥B ⧸ Q) * h
  obtain ⟨yκ, hyκ⟩ : ∃ z : ↥B ⧸ Q, z = redκ y := ⟨_, rfl⟩
  have hlaκ : xκ * ((16 * yκ) ^ 2 * (16 * yκ - 1) ^ 2) = 256 * ((16 * yκ) ^ 2 - 16 * yκ + 1) ^ 3 := by

    have hA : x * den = num := by
      show num * u * den = num
      rw [mul_assoc, mul_comm u den, hu, mul_one]
    have h := congrArg redκ hA
    simp only [den, num, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat] at h
    rw [← hxκ, ← hyκ] at h
    exact h

  have hroot := level_two_root_cases (q := q) hq xκ h01728κ yκ hlaκ m hsexκ

  let c16 : ↥(coeffSubring A K) := ⟨(16 : (AlgebraicClosure ℚ))⁻¹, h16mem⟩
  have hc16 : (16 : ↥(coeffSubring A K)) * c16 = 1 := Subtype.ext (by push_cast; exact mul_inv_cancel₀ (by norm_num))
  have h2mem : (2 : (AlgebraicClosure ℚ))⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 1; rwa [pow_one] at this
  let c2 : ↥(coeffSubring A K) := ⟨(2 : (AlgebraicClosure ℚ))⁻¹, h2mem⟩
  have hc2 : (2 : ↥(coeffSubring A K)) * c2 = 1 := Subtype.ext (by push_cast; exact mul_inv_cancel₀ (by norm_num))

  have hκ16 : redκ c16 = 16⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_)
    have := congrArg redκ hc16; rwa [map_mul, map_ofNat, map_one] at this
  have hk16 : redRestrict red K c16 = 16⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_)
    have := congrArg (redRestrict red K) hc16; rwa [map_mul, map_ofNat, map_one] at this
  have hκ2 : redκ c2 = 2⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_)
    have := congrArg redκ hc2; rwa [map_mul, map_ofNat, map_one] at this
  have hk2 : redRestrict red K c2 = 2⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_)
    have := congrArg (redRestrict red K) hc2; rwa [map_mul, map_ofNat, map_one] at this

  obtain ⟨y', hy'm, hla'⟩ : ∃ y' : ↥(coeffSubring A K), redκ y' = m ∧
      a * ((16 * redRestrict red K y') ^ 2 * (16 * redRestrict red K y' - 1) ^ 2)
        = 256 * ((16 * redRestrict red K y') ^ 2 - 16 * redRestrict red K y' + 1) ^ 3 := by
    rcases hroot with ⟨hx0, hm0⟩ | ⟨hx1728, hm1728⟩
    ·
      have ha0 : a = 0 := by
        rcases h01728 with h | h
        · exact h
        · exfalso
          have h' : xκ = 1728 := by
            have := hredκ (x - 1728) (by rw [map_sub, hx, h, map_ofNat, sub_self])
            rw [map_sub, map_ofNat, sub_eq_zero] at this; rw [hxκ]; exact this
          rw [hx0] at h'

          have h2 : (2 : ↥B ⧸ Q) ≠ 0 := by
            intro h2
            have := (CharP.cast_eq_zero_iff (↥B ⧸ Q) q 2).mp (by exact_mod_cast h2)
            have := Nat.le_of_dvd (by norm_num) this; omega
          have h3 : (3 : ↥B ⧸ Q) ≠ 0 := by
            intro h3
            have := (CharP.cast_eq_zero_iff (↥B ⧸ Q) q 3).mp (by exact_mod_cast h3)
            have := Nat.le_of_dvd (by norm_num) this; omega
          have : (1728 : ↥B ⧸ Q) = 2 ^ 6 * 3 ^ 3 := by norm_num
          exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) (this ▸ h'.symm)
      have hl0 : (16 * l) ^ 2 - 16 * l + 1 = 0 := by
        rw [ha0, zero_mul] at hla
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp hla.symm).resolve_left h256k)
      rcases hm0 with hmy | hmy
      · exact ⟨y, by rw [← hyκ]; exact hmy.symm, by rw [hy]; exact hla⟩
      · refine ⟨c16 - y, ?_, ?_⟩
        · rw [map_sub, hκ16, ← hyκ]; exact hmy.symm
        · rw [map_sub, hk16, hy, ha0, zero_mul]
          have : (16 * (16⁻¹ - l)) ^ 2 - 16 * (16⁻¹ - l) + 1 = (16 * l) ^ 2 - 16 * l + 1 := by
            have h16inv : (16 : k) * 16⁻¹ = 1 := mul_inv_cancel₀ h16k
            linear_combination (16 * 16⁻¹ - 1 - 2 * (16 * l) + 1) * h16inv
          rw [this, hl0]; norm_num
    ·
      have ha1728 : a = 1728 := by
        rcases h01728 with h | h
        · exfalso
          have h' : xκ = 0 := by rw [hxκ]; exact hredκ x (by rw [hx, h])
          rw [hx1728] at h'
          have h2 : (2 : ↥B ⧸ Q) ≠ 0 := by
            intro h2
            have := (CharP.cast_eq_zero_iff (↥B ⧸ Q) q 2).mp (by exact_mod_cast h2)
            have := Nat.le_of_dvd (by norm_num) this; omega
          have h3 : (3 : ↥B ⧸ Q) ≠ 0 := by
            intro h3
            have := (CharP.cast_eq_zero_iff (↥B ⧸ Q) q 3).mp (by exact_mod_cast h3)
            have := Nat.le_of_dvd (by norm_num) this; omega
          have : (1728 : ↥B ⧸ Q) = 2 ^ 6 * 3 ^ 3 := by norm_num
          exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) (this ▸ h')
        · exact h

      have hD : ∀ t : k, (16 * t + 1) * (16 * t - 2) * (2 * (16 * t) - 1) = 0 →
          a * ((16 * t) ^ 2 * (16 * t - 1) ^ 2) = 256 * ((16 * t) ^ 2 - 16 * t + 1) ^ 3 := by
        intro t ht
        rw [ha1728]
        have key : (256 : k) * ((16 * t) ^ 2 - 16 * t + 1) ^ 3 - 1728 * ((16 * t) ^ 2 * (16 * t - 1) ^ 2)
            = 64 * ((16 * t + 1) * (16 * t - 2) * (2 * (16 * t) - 1)) ^ 2 := by ring
        rw [ht] at key
        have : (256 : k) * ((16 * t) ^ 2 - 16 * t + 1) ^ 3 - 1728 * ((16 * t) ^ 2 * (16 * t - 1) ^ 2) = 0 := by
          rw [key]; ring
        exact (sub_eq_zero.mp this).symm
      have h16invk : (16 : k) * 16⁻¹ = 1 := mul_inv_cancel₀ h16k
      have h2invk : (2 : k) * 2⁻¹ = 1 := mul_inv_cancel₀ h2k
      rcases hm1728 with hmv | hmv | hmv
      · refine ⟨-c16, ?_, hD _ ?_⟩
        · rw [map_neg, hκ16]; exact hmv.symm
        · rw [map_neg, hk16]
          have : (16 : k) * -16⁻¹ + 1 = 0 := by linear_combination (-1 : k) * h16invk
          rw [this, zero_mul, zero_mul]
      · refine ⟨2 * c16, ?_, hD _ ?_⟩
        · rw [map_mul, map_ofNat, hκ16, hmv]

          have h8 : (8 : ↥B ⧸ Q) * (2 * 16⁻¹) = 1 := by
            have h16κ : (16 : ↥B ⧸ Q) * 16⁻¹ = 1 := by
              rw [← hκ16]; have := congrArg redκ hc16; rwa [map_mul, map_ofNat, map_one] at this
            linear_combination h16κ
          exact (eq_inv_of_mul_eq_one_right h8).symm ▸ rfl
        · rw [map_mul, map_ofNat, hk16]
          have : (16 : k) * (2 * 16⁻¹) - 2 = 0 := by linear_combination (2 : k) * h16invk
          rw [this, mul_zero, zero_mul]
      · refine ⟨c16 * c2, ?_, hD _ ?_⟩
        · rw [map_mul, hκ16, hκ2, hmv]
          have h32 : (32 : ↥B ⧸ Q) * (16⁻¹ * 2⁻¹) = 1 := by
            have h16κ : (16 : ↥B ⧸ Q) * 16⁻¹ = 1 := by
              rw [← hκ16]; have := congrArg redκ hc16; rwa [map_mul, map_ofNat, map_one] at this
            have h2κ : (2 : ↥B ⧸ Q) * 2⁻¹ = 1 := by
              rw [← hκ2]; have := congrArg redκ hc2; rwa [map_mul, map_ofNat, map_one] at this
            linear_combination (2 * 2⁻¹ : ↥B ⧸ Q) * h16κ + h2κ
          exact (eq_inv_of_mul_eq_one_right h32).symm ▸ rfl
        · rw [map_mul, hk16, hk2]
          have : (2 : k) * (16 * (16⁻¹ * 2⁻¹)) - 1 = 0 := by
            linear_combination (2 * 2⁻¹ : k) * h16invk + h2invk
          rw [this, mul_zero]

  have hmq_sq : mq ^ (q ^ 2) = mq :=
    pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq xκ h01728κ mq hsexqκ
  obtain ⟨data, hKr⟩ := ModularCurve.exists_lambdaKroneckerCongruence q hq2
  have hΨB : evB (psiT (coeffSubring A K) data) = 0 := by
    apply Subtype.ext
    rw [evB_coe, lambdaEval_psiT]; rfl
  let χ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥B ⧸ Q := π.comp evB
  have hχ0 : χ (MvPolynomial.X 0) = m := by rw [hm]; rfl
  have hχ1 : χ (MvPolynomial.X 1) = mq := by rw [hmq]; rfl
  let θκ : Polynomial ℤ →+* ↥B ⧸ Q := Polynomial.eval₂RingHom (Int.castRingHom _) m
  have hχΨ : χ (psiT (coeffSubring A K) data) = data.Ψ.eval₂ θκ mq := by
    rw [psiT, Polynomial.hom_eval₂, hχ1]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast, θκ]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hχ0]
      simp only [θκ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

  obtain ⟨ρ, hρd⟩ : ∃ ρ : Polynomial (Polynomial (ZMod q)) →+* ↥B ⧸ Q,
      ρ = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl q) (↥B ⧸ Q)) m) mq := ⟨_, rfl⟩
  have hρΨ : ρ (reduceModBivar q data.Ψ) = data.Ψ.eval₂ θκ mq := by
    have hcomp : ρ.comp (reduceModBivar q) = Polynomial.eval₂RingHom θκ mq := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
        simp [hρd, reduceModBivar, θκ]
      · simp [hρd, reduceModBivar, θκ]
    have := congrArg (fun g => g data.Ψ) hcomp
    simpa using this
  have hprod : (m ^ q - mq) * (m - mq ^ q) = 0 := by
    have h0 : data.Ψ.eval₂ θκ mq = 0 := by
      rw [← hχΨ]
      show π (evB (psiT (coeffSubring A K) data)) = 0
      rw [hΨB, map_zero]
    rw [← hρΨ, hKr, map_mul] at h0
    have e1 : ρ (Polynomial.C Polynomial.X ^ q - Polynomial.X) = m ^ q - mq := by
      rw [hρd]; simp [Polynomial.eval₂_pow]
    have e2 : ρ (Polynomial.C Polynomial.X - Polynomial.X ^ q) = m - mq ^ q := by
      rw [hρd]; simp [Polynomial.eval₂_pow]
    rw [e1, e2] at h0
    exact h0
  have hmq : mq = m ^ q := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (sub_eq_zero.mp h).symm
    · have hm' : m = mq ^ q := sub_eq_zero.mp h
      rw [hm', ← pow_mul, ← pow_two, hmq_sq]

  refine ⟨redRestrict red K y', hla', y', rfl, ?_, ?_, ?_⟩
  · intro b hb
    have : b = cB ϖ := Subtype.ext (by rw [hb, cB_coe]; rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl)
    rw [this]; exact hϖQ
  · intro b hb
    have hb' : b = evB (MvPolynomial.X 0 - MvPolynomial.C y') := Subtype.ext (by rw [hb]; rfl)
    rw [hb', ← Ideal.Quotient.eq_zero_iff_mem]
    show χ (MvPolynomial.X 0 - MvPolynomial.C y') = 0
    rw [map_sub, hχ0]
    show m - redκ y' = 0
    rw [hy'm, sub_self]
  · intro b hb
    have hb' : b = evB (MvPolynomial.X 1 - MvPolynomial.C (y' ^ q)) := Subtype.ext (by rw [hb]; rfl)
    rw [hb', ← Ideal.Quotient.eq_zero_iff_mem]
    show χ (MvPolynomial.X 1 - MvPolynomial.C (y' ^ q)) = 0
    rw [map_sub, hχ1]
    show mq - redκ (y' ^ q) = 0
    rw [map_pow, hy'm, hmq, sub_self]

end

end S_ModularCurve_LambdaNodeLocalized_exists_level_two_value_sub_const_mem_of_isMaximal
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_level_two_value_sub_const_mem_of_isMaximal (solution)
