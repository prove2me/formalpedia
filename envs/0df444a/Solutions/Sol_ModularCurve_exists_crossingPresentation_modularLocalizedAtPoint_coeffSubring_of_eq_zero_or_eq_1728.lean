-- Prove2me | solution 1 for ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/83c62aa4-61a5-5bd4-a8f7-7f558e1dd84a

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728
import Theorems.Thm_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic
import Theorems.Thm_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.NodeLocalized.coe_modularEvalAt AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728.ModularCurve"
open ModularCurve.NodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.coeffSubring NodeLocalized.redRestrict ssJSet jWidth jWidth_pos UVCrossingModel UVCrossingModel.const exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728 exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace WideAssembly

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

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

theorem irreducible_and_natCast_eq_of_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime]
    [CharP k q] [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    Irreducible ϖ ∧ ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  have hmax : maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := by
    ext c
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton,
      isUnit_coeffSubring_iff red K q c, not_not, hϖ c]
    exact Iff.rfl
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  refine ⟨hirr, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hirr
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

theorem inv_two_pow_mem (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (hq : 5 ≤ q) (n : ℕ) : ((2 : Qb) ^ n)⁻¹ ∈ coeffSubring A K := by
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
    first | simpa using h1 | (push_cast at h1 ⊢; exact h1) | (norm_num at h1 ⊢; exact h1)
  have : ((2 : Qb) ^ n)⁻¹ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [this]; exact SetLike.coe_mem _

end RedLemmas

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

section Frame
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] [CharP k q] [DecidableEq k]
  (red : A →+* k) (a : k) (K : IntermediateField ℚ Qb) (ϖ : ↥(coeffSubring A K))

abbrev WideConcl : Prop :=
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
      ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
        IsUnit w ∧
        G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w ∧
        (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
          IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
            Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) ∧
        (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
        (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
        H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} ∧
        G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} ∧
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}

end Frame

section HL
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]

omit [Fact q.Prime] in
theorem two_ne_zero_k (hq : 5 ≤ q) [Fact q.Prime] : (2 : k) ≠ 0 := by
  rw [show (2 : k) = ((2 : ℕ) : k) by norm_cast, Ne, CharP.cast_eq_zero_iff k q]
  intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega

omit [Fact q.Prime] in
theorem three_ne_zero_k (hq : 5 ≤ q) [Fact q.Prime] : (3 : k) ≠ 0 := by
  rw [show (3 : k) = ((3 : ℕ) : k) by norm_cast, Ne, CharP.cast_eq_zero_iff k q]
  intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega

theorem exists_lift_of_two_pow_mul_eq (red : A →+* k) (K : IntermediateField ℚ Qb) (hq : 5 ≤ q)
    (n : ℕ) (m : ℤ) (l : k) (h : (2 : k) ^ n * l = m) :
    ∃ y : ↥(coeffSubring A K), redRestrict red K y = l := by
  have h2 : (2 : k) ≠ 0 := two_ne_zero_k (k := k) (q := q) hq
  refine ⟨(m : ↥(coeffSubring A K)) * ⟨((2 : Qb) ^ n)⁻¹, inv_two_pow_mem red K q hq n⟩, ?_⟩
  have hinv : redRestrict red K ⟨((2 : Qb) ^ n)⁻¹, inv_two_pow_mem red K q hq n⟩ = ((2 : k) ^ n)⁻¹ := by
    have hprod : (⟨((2 : Qb) ^ n)⁻¹, inv_two_pow_mem red K q hq n⟩ : ↥(coeffSubring A K)) * (2 ^ n) = 1 := by
      apply Subtype.ext
      push_cast
      exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
    have h1 := congrArg (redRestrict red K) hprod
    rw [map_mul, map_pow, map_ofNat, map_one] at h1
    exact (eq_inv_of_mul_eq_one_left h1)
  rw [map_mul, map_intCast, hinv, ← h]
  field_simp

theorem hl_of_eq_1728 (red : A →+* k) (K : IntermediateField ℚ Qb) (hq : 5 ≤ q) (a : k) (ha : a = 1728) :
    ∀ l : k, l ^ (q ^ 2) = l → a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      ∃ y : ↥(coeffSubring A K), redRestrict red K y = l := by
  intro l _ hla
  subst ha
  have h2 : (2 : k) ≠ 0 := two_ne_zero_k (k := k) (q := q) hq
  have h256 : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have hP : 4096 * l ^ 3 - 384 * l ^ 2 - 24 * l + 1 = 0 := by
    have h0 : 256 * (4096 * l ^ 3 - 384 * l ^ 2 - 24 * l + 1) ^ 2 = 0 := by
      linear_combination (-1 : k) * hla
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h0).resolve_left h256)
  have hfac : (16 * l + 1) * ((8 * l - 1) * (32 * l - 1)) = 0 := by linear_combination hP
  rcases mul_eq_zero.mp hfac with h1 | h23
  · exact exists_lift_of_two_pow_mul_eq red K hq 4 (-1) l (by push_cast; linear_combination h1)
  · rcases mul_eq_zero.mp h23 with h2' | h3
    · exact exists_lift_of_two_pow_mul_eq red K hq 3 1 l (by push_cast; linear_combination h2')
    · exact exists_lift_of_two_pow_mul_eq red K hq 5 1 l (by push_cast; linear_combination h3)

theorem hl_of_eq_zero_of_root (red : A →+* k) (K : IntermediateField ℚ Qb) (hq : 5 ≤ q) (a : k) (ha : a = 0)
    (c : ↥(coeffSubring A K)) (hc : redRestrict red K (c ^ 2 + c + 1) = 0) :
    ∀ l : k, l ^ (q ^ 2) = l → a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      ∃ y : ↥(coeffSubring A K), redRestrict red K y = l := by
  intro l _ hla
  subst ha
  have h2 : (2 : k) ≠ 0 := two_ne_zero_k (k := k) (q := q) hq
  have h256 : (256 : k) ≠ 0 := by
    have : (256 : k) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have hD : (16 * l) ^ 2 - 16 * l + 1 = 0 := by
    have h0 : 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 = 0 := by rw [← hla]; ring
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp h0).resolve_left h256)
  set cb := redRestrict red K c with hcb
  have hc' : cb ^ 2 + cb + 1 = 0 := by
    have := hc; rw [map_add, map_add, map_pow, map_one] at this; exact this
  have hfac : (16 * l + cb) * (16 * l - cb - 1) = 0 := by linear_combination hD - hc'
  rcases mul_eq_zero.mp hfac with h1 | h1
  ·
    obtain ⟨y, hy⟩ := exists_lift_of_two_pow_mul_eq red K hq 4 (-1) (l * cb⁻¹ ) (by
      have hcb0 : cb ≠ 0 := by rintro h0; rw [h0] at hc'; norm_num at hc'
      push_cast
      field_simp
      linear_combination h1)
    refine ⟨y * c, ?_⟩
    have hcb0 : cb ≠ 0 := by rintro h0; rw [h0] at hc'; norm_num at hc'
    rw [map_mul, hy, ← hcb, mul_assoc, inv_mul_cancel₀ hcb0, mul_one]
  ·
    have hcb1 : cb + 1 ≠ 0 := by
      intro h0
      have : cb = -1 := by linear_combination h0
      rw [this] at hc'; norm_num at hc'
    obtain ⟨y, hy⟩ := exists_lift_of_two_pow_mul_eq red K hq 4 1 (l * (cb + 1)⁻¹) (by
      push_cast
      field_simp
      linear_combination h1)
    refine ⟨y * (c + 1), ?_⟩
    rw [map_mul, map_add, map_one, hy, ← hcb, mul_assoc, inv_mul_cancel₀ hcb1, mul_one]

end HL

section CaseA
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem caseA (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (hl : ∀ l : k, l ^ (q ^ 2) = l → a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      ∃ y : ↥(coeffSubring A K), redRestrict red K y = l) :
    WideConcl q A red a K ϖ := by
  classical
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := stepA_dvr red K q
  obtain ⟨hirr, eK, ε, heK, hε, hqϖ⟩ := irreducible_and_natCast_eq_of_uniformizer red K q ϖ hϖ
  obtain ⟨hnoeth, hloc, -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hnoeth
  haveI := hloc

  obtain ⟨hprime, hpir, hlocW, hϖW⟩ := W_facts ϖ hirr
  haveI := hprime
  haveI : IsDomain (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := Ideal.Quotient.isDomain _
  haveI := hpir
  haveI := hlocW
  set ϖW : PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ := Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ) with hϖWdef
  haveI : IsDiscreteValuationRing (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    ⟨fun h0 => hϖW.ne_zero (by
      have hmem : ϖW ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := hϖW.not_isUnit
      rw [h0] at hmem
      exact hmem)⟩
  have hmaxW : maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) = Ideal.span {ϖW} := hϖW.maximalIdeal_eq
  have hmkX : Ideal.Quotient.mk (IW ϖ) PowerSeries.X = ϖW := by
    rw [hϖWdef, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hmaxW' : maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)
      = (Ideal.span {PowerSeries.X}).map (Ideal.Quotient.mk (IW ϖ)) := by
    rw [hmaxW, Ideal.map_span, Set.image_singleton, hmkX]
  haveI : IsPrecomplete (maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)) (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) := by
    rw [hmaxW']; exact isPrecomplete_map_mk _ _
  haveI : IsAdicComplete (maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ)) (PowerSeries ↥(coeffSubring A K) ⧸ IW ϖ) :=
    { }

  obtain ⟨θ, ι, -, hθC, hιC, hg, hh⟩ :=
    ModularCurve.exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728
      red a ha ha2 hq h01728 K x hx ϖ hϖ eK ε heK hε hqϖ hl

  have hE : 1 ≤ jWidth a * eK := Nat.succ_le_of_lt (Nat.mul_pos (jWidth_pos a) heK)
  have hϖι : ι (algebraMap _ _ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))))
      = UVCrossingModel.const (ϖW ^ (jWidth a * eK)) ϖW := by
    rw [← hθC ϖ]; exact hιC _
  obtain ⟨G', H', w, hw, hGH, hm, hp1, hp2, hn1, hn2, hs1, hs2⟩ :=
    IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
      ϖW hϖW (jWidth a * eK) hE ι _ _ _ hϖι hg hh
  refine ⟨eK, ε, heK, hε, hqϖ, G', H', w, hw, hGH, ?_, hp1, hp2, hn1, hn2, hs1, hs2⟩
  intro inst
  have : inst = hloc := Subsingleton.elim _ _
  subst this
  exact hm

end CaseA

end WideAssembly
end ModularCurve

end

open ModularCurve.WideAssembly in

theorem redRestrict_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : ModularCurve.NodeLocalized.coeffSubring A K ≤ ModularCurve.NodeLocalized.coeffSubring A K')
    (c : ↥(ModularCurve.NodeLocalized.coeffSubring A K)) :
    ModularCurve.NodeLocalized.redRestrict red K' (Subring.inclusion hle c) = ModularCurve.NodeLocalized.redRestrict red K c := rfl

open ModularCurve.WideAssembly in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  classical
  rcases h01728 with h0 | h1728
  · by_cases hroot : ∃ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 + c + 1) = 0
    · obtain ⟨c, hc⟩ := hroot
      exact caseA red a ha ha2 hq (Or.inl h0) K x hx ϖ hϖ (hl_of_eq_zero_of_root red K hq a h0 c hc)
    · push Not at hroot
      obtain ⟨K', hfin, hle, ζ, hζ, hbasis, hϖ'⟩ :=
        ModularCurve.NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot red K ϖ hϖ hroot
      haveI := hfin
      have hx' : redRestrict red K' (Subring.inclusion hle x) = a := by rw [redRestrict_inclusion]; exact hx
      have hζ' : redRestrict red K' (ζ ^ 2 + ζ + 1) = 0 := by rw [hζ, map_zero]
      have hK' := caseA red a ha ha2 hq (Or.inl h0) K' (Subring.inclusion hle x) hx' (Subring.inclusion hle ϖ) hϖ'
        (hl_of_eq_zero_of_root red K' hq a h0 ζ hζ')
      refine ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic
        red a ha ha2 hq K x hx ϖ hϖ K' hle ζ (-1) (-1) ?_ ?_ hbasis hϖ' hK'
      · rw [map_neg, map_one]; linear_combination hζ
      · intro c
        have : c ^ 2 - (-1) * c - (-1) = c ^ 2 + c + 1 := by ring
        rw [this]; exact hroot c
  · exact caseA red a ha ha2 hq (Or.inr h1728) K x hx ϖ hϖ (hl_of_eq_1728 red K hq a h1728)

end S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 (solution)
