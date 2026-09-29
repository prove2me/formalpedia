-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c29beb3a-845a-5134-bf98-0e59dbf559bb

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_mul_eq_of_mem_lambdaFieldOver
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
import Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver qExpand_two_jq_mul_lambdaModC_sq NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two LambdaNodeLocalized.qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace Ws30EBAssembly

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
    first | simpa using h1 | (push_cast at h1 ⊢; exact h1) | exact_mod_cast h1
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

section MainEB
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem mainEB (hq : 5 ≤ q) (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (B : Subring LQ)
    (hB : ∀ z : LQ, z ∈ B ↔
      z ∈ lambdaFieldOver q K ∧ ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem z)
    [IsLocalRing ↥(SL q A red l K)] :
    (∀ z ∈ R₀ q A red a K, qExpand Qb 2 z ∈ B) ∧
    (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B) ∧
    ∃ hBS : B ≤ SL q A red l K,
      letI : Algebra ↥B ↥(SL q A red l K) := (Subring.inclusion hBS).toAlgebra
      ((IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)).IsMaximal ∧
      IsLocalization.AtPrime ↥(SL q A red l K) ((IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)) ∧
      (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) p = 0 →
        ∀ hp : lambdaEval q (coeffSubring A K) p ∈ B,
          (⟨lambdaEval q (coeffSubring A K) p, hp⟩ : ↥B) ∈
            (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS)) := by
  classical
  have hq2 : q ≠ 2 := by omega
  have hl2 : l ^ (q ^ 2) = l := pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l hla

  have h2k : (2 : k) ≠ 0 := by
    rw [Ne, show (2 : k) = ((2 : ℕ) : k) by norm_cast, CharP.cast_eq_zero_iff k q]
    intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h256 : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2k
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply h256; simpa using hla.symm
  have hl1 : 16 * l ≠ 1 := by
    intro h
    apply h256
    have := hla; rw [h] at this; simpa using this.symm
  have hl1' : 16 * l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have hval : a * (l ^ 2 * (16 * l - 1) ^ 2) = (256 * l ^ 2 - 16 * l + 1) ^ 3 := by
    have h' : (256 : k) * (a * (l ^ 2 * (16 * l - 1) ^ 2)) = 256 * (256 * l ^ 2 - 16 * l + 1) ^ 3 := by
      linear_combination hla
    exact mul_left_cancel₀ h256 h'

  have hvalq : a ^ q * ((l ^ q) ^ 2 * (16 * l ^ q - 1) ^ 2) = (256 * (l ^ q) ^ 2 - 16 * l ^ q + 1) ^ 3 := by
    have h' := congrArg (frobenius k q) hval
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat] at h'
    simpa only [frobenius_def] using h'

  have hB0 : ∀ z ∈ R₀ q A red a K, qExpand Qb 2 z ∈ B := by
    intro z hz
    rw [hB]
    refine ⟨?_, ?_⟩
    · exact ModularCurve.LambdaNodeLocalized.qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver q K
        (R₀_le_fieldOver q A red a K hz)
    · exact RingHom.isIntegralElem_map _ (x := (⟨z, hz⟩ : ↥(R₀ q A red a K)))

  have hev0 : ((ev q A red a K (MvPolynomial.X 0) : ↥(R₀ q A red a K)) : LQ) = jqModC Qb := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hev1 : ((ev q A red a K (MvPolynomial.X 1) : ↥(R₀ q A red a K)) : LQ) = jqNModC Qb (1 * q) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hlev0 : lev q A K (MvPolynomial.X 0) = lambdaModC Qb := by
    show lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hlev1 : lev q A K (MvPolynomial.X 1) = lambdaNModC Qb q := by
    show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hlevC : ∀ c : ↥(coeffSubring A K), lev q A K (MvPolynomial.C c) = algebraMap Qb LQ (c : Qb) := by
    intro c
    show lambdaEval q (coeffSubring A K) (MvPolynomial.C c) = _
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl

  have hμint : ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (lambdaModC Qb) :=
    isIntegralElem_of_jRel q A K red a hq (ev q A red a K (MvPolynomial.X 0)) (lambdaModC Qb)
      (by rw [hev0]; exact jLambda_Qb)
  have hμqint : ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (lambdaNModC Qb q) :=
    isIntegralElem_of_jRel q A K red a hq (ev q A red a K (MvPolynomial.X 1)) (lambdaNModC Qb q)
      (by rw [hev1]; exact jLambda_Qb_q (q := q))

  have hB1 : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      have : lambdaEval q (coeffSubring A K) (MvPolynomial.C c) =
          qExpand Qb 2 ((ev q A red a K (MvPolynomial.C c) : ↥(R₀ q A red a K)) : LQ) := by
        rw [ev_C_coe, qExpand_algebraMap]; exact hlevC c
      rw [this]; exact hB0 _ (ev q A red a K (MvPolynomial.C c)).2
    | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [hB]
      fin_cases i
      · refine ⟨?_, ?_⟩
        · show lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) ∈ _
          rw [show lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = lambdaModC Qb from hlev0]
          exact lambdaModC_mem_lambdaFieldOver q K
        · show ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (lambdaEval q (coeffSubring A K) (MvPolynomial.X 0))
          rw [show lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = lambdaModC Qb from hlev0]; exact hμint
      · refine ⟨?_, ?_⟩
        · show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) ∈ _
          rw [show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = lambdaNModC Qb q from hlev1]
          exact lambdaNModC_mem_lambdaFieldOver q K
        · show ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (lambdaEval q (coeffSubring A K) (MvPolynomial.X 1))
          rw [show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = lambdaNModC Qb q from hlev1]; exact hμqint

  have hpev0 : pev q red l K (MvPolynomial.X 0) = l := by
    show pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.X 0) = l
    rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hpev1 : pev q red l K (MvPolynomial.X 1) = l ^ q := by
    show pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.X 1) = l ^ q
    rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hpevC : ∀ c : ↥(coeffSubring A K), pev q red l K (MvPolynomial.C c) = redRestrict red K c := by
    intro c
    show pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) (MvPolynomial.C c) = _
    rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

  have hφj : HasVal q A red l K (qExpand Qb 2 (jqModC Qb)) a := by
    refine ⟨(256 * MvPolynomial.X 0 ^ 2 - 16 * MvPolynomial.X 0 + 1) ^ 3,
      MvPolynomial.X 0 ^ 2 * (16 * MvPolynomial.X 0 - 1) ^ 2, ?_, ?_, ?_⟩
    · simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, hpev0]
      exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl1')
    · simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hlev0]
      linear_combination jLambda_Qb
    · simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hpev0]
      linear_combination hval
  have hφjq : HasVal q A red l K (qExpand Qb 2 (jqNModC Qb (1 * q))) (a ^ q) := by
    refine ⟨(256 * MvPolynomial.X 1 ^ 2 - 16 * MvPolynomial.X 1 + 1) ^ 3,
      MvPolynomial.X 1 ^ 2 * (16 * MvPolynomial.X 1 - 1) ^ 2, ?_, ?_, ?_⟩
    · simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, hpev1]
      refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hl0)) (pow_ne_zero _ ?_)

      have : (16 * l ^ q - 1 : k) = (16 * l - 1) ^ q := by
        have h' := (frobenius_def (p := q) (16 * l - 1)).symm
        simp only [map_mul, map_sub, map_one, map_ofNat] at h'
        simpa only [frobenius_def] using h'.symm
      rw [this]; exact pow_ne_zero _ hl1'
    · simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hlev1]
      linear_combination jLambda_Qb_q (q := q)
    · simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hpev1]
      linear_combination hvalq

  have hφev : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      HasVal q A red l K (qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) p))
        (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h1 : qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c)) = lev q A K (MvPolynomial.C c) := by
        have := ev_C_coe q A K red a c
        rw [show ((ev q A red a K (MvPolynomial.C c) : ↥(R₀ q A red a K)) : LQ) =
          modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) from rfl] at this
        rw [this, qExpand_algebraMap, hlevC]
      have h2 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) = pev q red l K (MvPolynomial.C c) := by
        rw [hpevC, pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [h1, h2]; exact hasVal_lev red l K _
    | add p p' hp hp' =>
      rw [map_add, map_add, map_add]; exact hasVal_add red l K hp hp'
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul]
      refine hasVal_mul red l K hp ?_
      fin_cases i
      · have e1 : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC Qb := by
          rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
        have e2 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0) = a := by
          rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
        show HasVal q A red l K (qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0)))
          (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0))
        rw [e1, e2]; exact hφj
      · have e1 : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = jqNModC Qb (1 * q) := by
          rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
        have e2 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1) = a ^ q := by
          rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
        show HasVal q A red l K (qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1)))
          (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1))
        rw [e1, e2]; exact hφjq

  have hφR : ∀ z ∈ R₀ q A red a K, ∃ v, HasVal q A red l K (qExpand Qb 2 z) v := by
    rintro z ⟨r, s, hs, hzs⟩
    have h1 := hφev s
    have hs0 : qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) s) ≠ 0 := ne_zero_of_hasVal red l K hq2 hl2 h1 hs
    have : qExpand Qb 2 z = qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) r) *
        (qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hzs]
    rw [this]
    exact ⟨_, hasVal_mul red l K (hφev r) (hasVal_inv red l K hq2 hl2 h1 hs)⟩
  have hφS : ∀ z ∈ R₀ q A red a K, qExpand Qb 2 z ∈ SL q A red l K := fun z hz => by
    obtain ⟨v, hv⟩ := hφR z hz; exact mem_SL_of_hasVal red l K hv

  haveI hIC : IsIntegrallyClosed ↥(SL q A red l K) :=
    ModularCurve.isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring hq red l hl2 hl0 hl1 ⟨a, ha, hla⟩ K ⟨y, hy⟩

  let ψ : ↥(R₀ q A red a K) →+* ↥(SL q A red l K) :=
    ((qExpand Qb 2).comp (R₀ q A red a K).subtype).codRestrict (SL q A red l K) (fun z => hφS z z.2)
  have hψcomp : (SL q A red l K).subtype.comp ψ = (qExpand Qb 2).comp (R₀ q A red a K).subtype := by
    ext z; rfl

  have hBS : B ≤ SL q A red l K := by
    intro b hb
    obtain ⟨hbL, P, hPm, hPb⟩ := (hB b).mp hb

    have hPb' : Polynomial.eval₂ (SL q A red l K).subtype b (P.map ψ) = 0 := by
      rw [Polynomial.eval₂_map, hψcomp]; exact hPb

    obtain ⟨y', z', hy', hz', hz0, hbz⟩ :=
      ModularCurve.LambdaNodeLocalized.exists_mul_eq_of_mem_lambdaFieldOver red l K hbL
    have hinj : Function.Injective ((SL q A red l K).subtype) := Subtype.val_injective
    let ι : FractionRing ↥(SL q A red l K) →+* LQ := IsFractionRing.lift (K := FractionRing ↥(SL q A red l K)) hinj
    have hιalg : ∀ s : ↥(SL q A red l K), ι (algebraMap ↥(SL q A red l K) (FractionRing ↥(SL q A red l K)) s) = (s : LQ) := fun s =>
      IsFractionRing.lift_algebraMap hinj s
    have hz0' : (⟨z', hz'⟩ : ↥(SL q A red l K)) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
    let w : FractionRing ↥(SL q A red l K) :=
      IsLocalization.mk' (FractionRing ↥(SL q A red l K)) (⟨y', hy'⟩ : ↥(SL q A red l K)) ⟨⟨z', hz'⟩, mem_nonZeroDivisors_of_ne_zero hz0'⟩
    have hιw : ι w = b := by
      show IsFractionRing.lift hinj _ = b
      rw [IsFractionRing.lift_mk']
      show (y' : LQ) / z' = b
      rw [eq_comm, eq_div_iff hz0]
      exact hbz
    have hιinj : Function.Injective ι := ι.injective
    have hwint : IsIntegral ↥(SL q A red l K) w := by
      refine ⟨P.map ψ, hPm.map ψ, ?_⟩
      apply hιinj
      rw [Polynomial.hom_eval₂, map_zero]
      have hcomp : ι.comp (algebraMap ↥(SL q A red l K) (FractionRing ↥(SL q A red l K))) = (SL q A red l K).subtype := RingHom.ext hιalg
      rw [hcomp, hιw]
      exact hPb'
    obtain ⟨s', hs'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(SL q A red l K)) (K := FractionRing ↥(SL q A red l K))).mp hwint
    have : b = (s' : LQ) := by rw [← hιw, ← hs', hιalg]
    rw [this]; exact s'.2
  refine ⟨hB0, hB1, hBS, ?_⟩

  letI : Algebra ↥B ↥(SL q A red l K) := (Subring.inclusion hBS).toAlgebra
  set 𝔓 : Ideal ↥B := (IsLocalRing.maximalIdeal ↥(SL q A red l K)).comap (Subring.inclusion hBS) with h𝔓
  have halgB : ∀ b : ↥B, algebraMap ↥B ↥(SL q A red l K) b = Subring.inclusion hBS b := fun b => rfl

  have hmem𝔓 : ∀ b : ↥B, b ∈ 𝔓 ↔ HasVal q A red l K (b : LQ) 0 := by
    intro b
    rw [h𝔓, Ideal.mem_comap, mem_maximalIdeal_iff_hasVal_zero red l K hq2 hl2]
    rfl

  have hpev_eval : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pev q red l K p = redRestrict red K (MvPolynomial.eval ![y, y ^ q] p) := by
    intro p
    have : (redRestrict red K).comp (MvPolynomial.eval ![y, y ^ q]) = pev q red l K := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval_C, hpevC]
      · rw [RingHom.comp_apply, MvPolynomial.eval_X]
        fin_cases i
        · show redRestrict red K (![y, y ^ q] 0) = pev q red l K (MvPolynomial.X 0)
          rw [hpev0]; exact hy
        · show redRestrict red K (![y, y ^ q] 1) = pev q red l K (MvPolynomial.X 1)
          rw [hpev1]
          show redRestrict red K (y ^ q) = l ^ q
          rw [map_pow, hy]
    rw [← this]; rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Ideal.isMaximal_iff]
    refine ⟨?_, ?_⟩
    · rw [hmem𝔓]
      intro h0
      have h1 : HasVal q A red l K (1 : LQ) (1 : k) := by
        have := hasVal_lev red l K (q := q) (A := A) (1 : MvPolynomial (Fin 2) ↥(coeffSubring A K))
        rwa [map_one, map_one] at this
      exact one_ne_zero (hasVal_unique red l K hq2 hl2 h1 h0)
    · intro J f hPJ hf hfJ
      obtain ⟨v, hv⟩ := exists_hasVal_of_mem red l K (hBS f.2)
      have hv0 : v ≠ 0 := by
        rintro rfl; exact hf ((hmem𝔓 f).mpr hv)
      obtain ⟨r, s, hs, hfs, hvs⟩ := hv
      have hr : pev q red l K r ≠ 0 := by rw [← hvs]; exact mul_ne_zero hv0 hs

      set cr := MvPolynomial.eval ![y, y ^ q] r with hcr
      set cs := MvPolynomial.eval ![y, y ^ q] s with hcs
      have hcr_red : redRestrict red K cr = pev q red l K r := (hpev_eval r).symm
      have hcs_red : redRestrict red K cs = pev q red l K s := (hpev_eval s).symm
      have hcru : IsUnit cr := (isUnit_coeffSubring_iff red K q cr).mpr (by rw [hcr_red]; exact hr)
      obtain ⟨ur, hur⟩ := hcru
      set c : ↥(coeffSubring A K) := cs * ↑ur⁻¹ with hc
      have hcval : redRestrict red K c * pev q red l K r = pev q red l K s := by
        rw [hc, map_mul, hcs_red, ← hcr_red, ← hur, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

      let g : ↥B := ⟨lev q A K (MvPolynomial.C c), hB1 _⟩
      have hg : HasVal q A red l K (g : LQ) v⁻¹ := by
        have := hasVal_lev red l K (q := q) (A := A) (MvPolynomial.C c)
        rw [hpevC] at this
        have hcv : redRestrict red K c = v⁻¹ := by
          refine eq_inv_of_mul_eq_one_left ?_
          have h3 : redRestrict red K c * (v * pev q red l K s) = pev q red l K s := by rw [hvs]; exact hcval
          have h4 : (redRestrict red K c * v) * pev q red l K s = 1 * pev q red l K s :=
            calc (redRestrict red K c * v) * pev q red l K s = redRestrict red K c * (v * pev q red l K s) := by ring
              _ = pev q red l K s := h3
              _ = 1 * pev q red l K s := (one_mul _).symm
          exact mul_right_cancel₀ hs h4
        rwa [hcv] at this

      have hfg : f * g - 1 ∈ 𝔓 := by
        rw [hmem𝔓]
        have h1 : HasVal q A red l K ((f : LQ) * (g : LQ)) (v * v⁻¹) :=
          hasVal_mul red l K ⟨r, s, hs, hfs, hvs⟩ hg
        rw [mul_inv_cancel₀ hv0] at h1
        have hneg : HasVal q A red l K (-1 : LQ) (-1 : k) := by
          have := hasVal_lev red l K (q := q) (A := A) (MvPolynomial.C (-1 : ↥(coeffSubring A K)))
          rwa [hlevC, hpevC, map_neg, map_one, Subring.coe_neg, Subring.coe_one, map_neg, map_one] at this
        have := hasVal_add red l K h1 hneg
        rw [add_neg_cancel] at this
        show HasVal q A red l K ((f : LQ) * (g : LQ) - 1) 0
        rwa [sub_eq_add_neg]
      have h1J : f * g - (f * g - 1) ∈ J := Submodule.sub_mem _ (J.mul_mem_right _ hfJ) (hPJ hfg)
      rwa [sub_sub_cancel] at h1J
  ·
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨x, hx⟩
      have hx' : Subring.inclusion hBS x ∉ IsLocalRing.maximalIdeal ↥(SL q A red l K) := hx
      rw [halgB]
      by_contra hnu
      exact hx' ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    · intro z
      obtain ⟨r, s, hs, hzs⟩ := z.2
      have hs𝔓 : (⟨lev q A K s, hB1 s⟩ : ↥B) ∉ 𝔓 := by
        rw [hmem𝔓]
        intro h0
        exact hs (hasVal_unique red l K hq2 hl2 (hasVal_lev red l K s) h0)
      refine ⟨⟨⟨lev q A K r, hB1 r⟩, ⟨⟨lev q A K s, hB1 s⟩, hs𝔓⟩⟩, ?_⟩
      rw [halgB, halgB]
      exact Subtype.ext hzs
    · intro x₁ x₂ hx
      refine ⟨1, ?_⟩
      rw [halgB, halgB] at hx
      have h' := congrArg (fun z : ↥(SL q A red l K) => (z : LQ)) hx
      have hxx : x₁ = x₂ := Subtype.ext h'
      rw [hxx]
  ·
    intro p hp0 hp
    rw [hmem𝔓]
    show HasVal q A red l K (lev q A K p) 0
    have := hasVal_lev red l K (q := q) (A := A) p
    rwa [show pev q red l K p = 0 from hp0] at this

end MainEB

end Ws30EBAssembly
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem.ModularCurve ModularCurve.Ws30EBAssembly in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (B : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hB : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ B ↔
      z ∈ lambdaFieldOver q K ∧ ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem z)
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))] :
    (∀ z ∈ (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), qExpand (AlgebraicClosure ℚ) 2 z ∈ B) ∧
    (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B) ∧
    ∃ hBS : B ≤ (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
      letI : Algebra ↥B ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) := (Subring.inclusion hBS).toAlgebra
      ((IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS)).IsMaximal ∧
      IsLocalization.AtPrime ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ((IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS)) ∧
      (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) p = 0 →
        ∀ hp : lambdaEval q (coeffSubring A K) p ∈ B,
          (⟨lambdaEval q (coeffSubring A K) p, hp⟩ : ↥B) ∈
            (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))).comap (Subring.inclusion hBS)) :=
  mainEB hq red a ha ha2 h01728 K l hla y hy B hB

end

end S_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_isLocalization_atPrime_lambdaLocalizedAtPoint_of_isIntegralElem (solution)
