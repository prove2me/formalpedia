-- Prove2me | solution 1 for ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f7e2ca4c-8915-51a4-8dc7-9f3649928a7a

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace RedIso

open IsLocalRing HahnSeries

section Core

variable {L : Type} [Field L] (A : ValuationSubring L)
variable {F : IntermediateField L (LaurentSeries L)} (W : ValuationSubring ↥F)

noncomputable abbrev upL (x : PowerSeries ↥A) : LaurentSeries L :=
  ofPowerSeries ℤ L (x.map (algebraMap ↥A L))

noncomputable abbrev dn (x : PowerSeries ↥A) : LaurentSeries (ResidueField ↥A) :=
  ofPowerSeries ℤ (ResidueField ↥A) (x.map (residue ↥A))

def IsGaussPresented : Prop :=
  ∀ f : ↥F, f ∈ W ↔ ∃ x y : PowerSeries ↥A, y.map (residue ↥A) ≠ 0 ∧ (f : LaurentSeries L) * upL A y = upL A x

variable {A W}

theorem upL_injective : Function.Injective (upL (L := L) A) := fun x y h =>
  PowerSeries.map_injective (algebraMap ↥A L) (FaithfulSMul.algebraMap_injective _ _) (ofPowerSeries_injective h)

theorem dn_ne_zero {y : PowerSeries ↥A} (hy : y.map (residue ↥A) ≠ 0) : dn A y ≠ 0 := fun h =>
  hy (ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h))

theorem cross_eq {f : LaurentSeries L} {x y x' y' : PowerSeries ↥A}
    (h : f * upL A y = upL A x) (h' : f * upL A y' = upL A x') : x * y' = x' * y := by
  apply upL_injective
  simp only [upL, map_mul] at h h' ⊢
  rw [← h, ← h']
  ring

theorem dn_cross {f : LaurentSeries L} {x y x' y' : PowerSeries ↥A}
    (h : f * upL A y = upL A x) (h' : f * upL A y' = upL A x') : dn A x * dn A y' = dn A x' * dn A y := by
  have := congrArg (dn A) (cross_eq h h')
  simpa only [dn, map_mul] using this

variable (hW : IsGaussPresented A W)
include hW

theorem exists_pres (f : ↥W) : ∃ x y : PowerSeries ↥A, y.map (residue ↥A) ≠ 0 ∧
    (((f : ↥F)) : LaurentSeries L) * upL A y = upL A x := (hW (f : ↥F)).mp f.2

noncomputable def redL (f : ↥W) : LaurentSeries (ResidueField ↥A) :=
  dn A (exists_pres hW f).choose / dn A (exists_pres hW f).choose_spec.choose

theorem redL_spec (f : ↥W) {x y : PowerSeries ↥A} (hy : y.map (residue ↥A) ≠ 0)
    (h : (((f : ↥F)) : LaurentSeries L) * upL A y = upL A x) : redL hW f * dn A y = dn A x := by
  obtain ⟨hy₀, h₀⟩ := (exists_pres hW f).choose_spec.choose_spec
  rw [redL, div_mul_eq_mul_div, div_eq_iff (dn_ne_zero hy₀), dn_cross h₀ h]

theorem redL_eq_div (f : ↥W) {x y : PowerSeries ↥A} (hy : y.map (residue ↥A) ≠ 0)
    (h : (((f : ↥F)) : LaurentSeries L) * upL A y = upL A x) : redL hW f = dn A x / dn A y := by
  rw [eq_div_iff (dn_ne_zero hy), redL_spec hW f hy h]

theorem redL_one : redL hW 1 = 1 := by
  have h : (((1 : ↥W) : ↥F) : LaurentSeries L) * upL A 1 = upL A 1 := by
    simp [upL]
  have := redL_spec hW 1 (y := 1) (by simp) h
  simpa [dn] using this

theorem redL_zero : redL hW 0 = 0 := by
  have h : (((0 : ↥W) : ↥F) : LaurentSeries L) * upL A 1 = upL A 0 := by
    simp [upL]
  have := redL_spec hW 0 (y := 1) (by simp) h
  simpa [dn] using this

theorem redL_mul (f g : ↥W) : redL hW (f * g) = redL hW f * redL hW g := by
  obtain ⟨x, y, hy, h⟩ := exists_pres hW f
  obtain ⟨x', y', hy', h'⟩ := exists_pres hW g
  have hyy : (y * y').map (residue ↥A) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hy hy'
  have hfg : (((f * g : ↥W) : ↥F) : LaurentSeries L) * upL A (y * y') = upL A (x * x') := by
    have e : (((f * g : ↥W) : ↥F) : LaurentSeries L) = ((f : ↥F) : LaurentSeries L) * ((g : ↥F) : LaurentSeries L) := by
      push_cast; rfl
    simp only [upL, map_mul] at h h' ⊢
    rw [e, ← h, ← h']; ring
  rw [redL_eq_div hW _ hyy hfg, redL_eq_div hW f hy h, redL_eq_div hW g hy' h']
  simp only [dn, map_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem redL_add (f g : ↥W) : redL hW (f + g) = redL hW f + redL hW g := by
  obtain ⟨x, y, hy, h⟩ := exists_pres hW f
  obtain ⟨x', y', hy', h'⟩ := exists_pres hW g
  have hyy : (y * y').map (residue ↥A) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hy hy'
  have hfg : (((f + g : ↥W) : ↥F) : LaurentSeries L) * upL A (y * y') = upL A (x * y' + y * x') := by
    have e : (((f + g : ↥W) : ↥F) : LaurentSeries L) = ((f : ↥F) : LaurentSeries L) + ((g : ↥F) : LaurentSeries L) := by
      push_cast; rfl
    simp only [upL, map_mul, map_add] at h h' ⊢
    rw [e, ← h, ← h']; ring
  rw [redL_eq_div hW _ hyy hfg, redL_eq_div hW f hy h, redL_eq_div hW g hy' h']
  simp only [dn, map_mul, map_add]
  exact (div_add_div _ _ (dn_ne_zero hy) (dn_ne_zero hy')).symm

noncomputable def redHom : ↥W →+* LaurentSeries (ResidueField ↥A) where
  toFun := redL hW
  map_one' := redL_one hW
  map_mul' := redL_mul hW
  map_zero' := redL_zero hW
  map_add' := redL_add hW

@[scoped simp] theorem redHom_apply (f : ↥W) : redHom hW f = redL hW f := rfl

theorem redL_eq_zero_iff (f : ↥W) {x y : PowerSeries ↥A} (hy : y.map (residue ↥A) ≠ 0)
    (h : (((f : ↥F)) : LaurentSeries L) * upL A y = upL A x) : redL hW f = 0 ↔ x.map (residue ↥A) = 0 := by
  rw [redL_eq_div hW f hy h, div_eq_zero_iff, or_iff_left (dn_ne_zero hy)]
  constructor
  · intro h0; exact ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
  · intro h0; rw [dn, h0, map_zero]

theorem ker_redHom : RingHom.ker (redHom hW) = maximalIdeal ↥W := by
  ext f
  rw [RingHom.mem_ker, redHom_apply, mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨x, y, hy, h⟩ := exists_pres hW f
  rw [redL_eq_zero_iff hW f hy h]
  constructor
  ·
    intro hx hu
    obtain ⟨u, rfl⟩ := hu
    obtain ⟨x', y', hy', h'⟩ := exists_pres hW (↑u⁻¹ : ↥W)
    have hprod : y * y' = x * x' := by
      apply upL_injective
      simp only [upL, map_mul] at h h' ⊢
      rw [← h, ← h']
      have e : (((↑u : ↥W) : ↥F) : LaurentSeries L) * (((↑u⁻¹ : ↥W) : ↥F) : LaurentSeries L) = 1 := by
        rw [← show ((((↑u * ↑u⁻¹ : ↥W)) : ↥F) : LaurentSeries L) = (((↑u : ↥W) : ↥F) : LaurentSeries L) * (((↑u⁻¹ : ↥W) : ↥F) : LaurentSeries L) from by push_cast; rfl,
          Units.mul_inv]
        rfl
      calc ofPowerSeries ℤ L (PowerSeries.map (algebraMap ↥A L) y) * ofPowerSeries ℤ L (PowerSeries.map (algebraMap ↥A L) y')
          = (((↑u : ↥W) : ↥F) : LaurentSeries L) * (((↑u⁻¹ : ↥W) : ↥F) : LaurentSeries L) *
              (ofPowerSeries ℤ L (PowerSeries.map (algebraMap ↥A L) y) * ofPowerSeries ℤ L (PowerSeries.map (algebraMap ↥A L) y')) := by
            rw [e, one_mul]
        _ = _ := by ring
    have := congrArg (PowerSeries.map (residue ↥A)) hprod
    rw [map_mul, map_mul, hx, zero_mul] at this
    exact mul_ne_zero hy hy' this
  ·
    intro hnu
    by_contra hx
    apply hnu
    have hf0 : ((f : ↥F) : LaurentSeries L) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      have : x = 0 := upL_injective (by rw [← h]; simp [upL])
      exact hx (by rw [this, map_zero])
    have hf0' : (f : ↥F) ≠ 0 := fun h0 => hf0 (by rw [h0]; rfl)
    have hinv : (f : ↥F)⁻¹ ∈ W := by
      rw [hW]
      refine ⟨y, x, hx, ?_⟩
      rw [show (((f : ↥F)⁻¹ : ↥F) : LaurentSeries L) = (((f : ↥F)) : LaurentSeries L)⁻¹ from by push_cast; rfl,
        inv_mul_eq_iff_eq_mul₀ hf0, h]
    exact ⟨⟨f, ⟨(f : ↥F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'), Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩

end Core

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    ModularCurve.coeffMap f (ofPowerSeries ℤ R u) = ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem map_map_int {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries ℤ) :
    (u.map (Int.castRingHom R)).map f = u.map (Int.castRingHom S) := by
  rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom R) u) = PowerSeries.map (f.comp (Int.castRingHom R)) u from
      (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom R) f)) u).symm,
    RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]

theorem map_map' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (u : PowerSeries R) :
    (u.map f).map g = u.map (g.comp f) :=
  (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp f g)) u).symm

theorem jqModC_mul_X (R : Type*) [CommRing R] :
    ModularCurve.jqModC R * ofPowerSeries ℤ R PowerSeries.X = ofPowerSeries ℤ R (ModularCurve.jNum.map (Int.castRingHom R)) := by
  rw [ModularCurve.jqModC, ofPowerSeries_X, mul_comm, ← mul_assoc, single_mul_single]
  simp

section Generators

variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable {F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))}
  {W : ValuationSubring ↥F} (hW : IsGaussPresented A W)

include hW in
theorem const_mem (a : ↥A) : algebraMap (AlgebraicClosure ℚ) ↥F (a : AlgebraicClosure ℚ) ∈ W := by
  rw [hW]
  refine ⟨PowerSeries.C a, 1, by simp, ?_⟩
  show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) * upL A 1 = upL A (PowerSeries.C a)
  simp only [upL, map_one, mul_one, PowerSeries.map_C, ofPowerSeries_C]
  rw [ModularCurve.algebraMap_laurentSeries_eq_single]
  rfl

noncomputable def constHom : ↥A →+* ↥W :=
  ((algebraMap (AlgebraicClosure ℚ) ↥F).comp A.subtype).codRestrict W.toSubring (fun a => const_mem A hW a)

@[scoped simp] theorem constHom_coe (a : ↥A) :
    (((constHom A hW a : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem redL_constHom (a : ↥A) :
    redL hW (constHom A hW a) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (residue ↥A a) := by
  have h : (((constHom A hW a : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) * upL A 1 = upL A (PowerSeries.C a) := by
    rw [constHom_coe]
    simp only [upL, map_one, mul_one, PowerSeries.map_C, ofPowerSeries_C]
    rw [ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  rw [redL_eq_div hW _ (y := 1) (by simp) h]
  simp only [dn, map_one, PowerSeries.map_C, ofPowerSeries_C, div_one]
  rw [ModularCurve.algebraMap_laurentSeries_eq_single]
  rfl

variable (jF : ↥F) (hjF : (jF : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))

include hW hjF in
theorem j_mem : jF ∈ W := by
  rw [hW]
  refine ⟨ModularCurve.jNum.map (Int.castRingHom ↥A), PowerSeries.X, ?_, ?_⟩
  · rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
  · rw [hjF, upL, upL, PowerSeries.map_X, map_map_int, jqModC_mul_X]

include hjF in
theorem redL_j : redL hW ⟨jF, j_mem A hW jF hjF⟩ = ModularCurve.jqModC (ResidueField ↥A) := by
  have h : (((⟨jF, j_mem A hW jF hjF⟩ : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) * upL A PowerSeries.X =
      upL A (ModularCurve.jNum.map (Int.castRingHom ↥A)) := by
    have e : (((⟨jF, j_mem A hW jF hjF⟩ : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = (jF : LaurentSeries (AlgebraicClosure ℚ)) := rfl
    rw [e, hjF, upL, upL, PowerSeries.map_X, map_map_int, jqModC_mul_X]
  have hX : (PowerSeries.X : PowerSeries ↥A).map (residue ↥A) ≠ 0 := by
    rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
  rw [redL_eq_div hW _ hX h, div_eq_iff (dn_ne_zero hX)]
  show ofPowerSeries ℤ (ResidueField ↥A) ((ModularCurve.jNum.map (Int.castRingHom ↥A)).map (residue ↥A)) =
    ModularCurve.jqModC (ResidueField ↥A) * ofPowerSeries ℤ (ResidueField ↥A) ((PowerSeries.X : PowerSeries ↥A).map (residue ↥A))
  rw [PowerSeries.map_X, map_map_int]
  exact (jqModC_mul_X (ResidueField ↥A)).symm

variable (Γ : Subgroup SL(2, ℤ))
  (hF : ∀ y ∈ ModularCurve.qExpFunctionFieldC ℚ Γ, ModularCurve.coeffEmb (AlgebraicClosure ℚ) y ∈ F)

theorem coeffEmb_intSeriesC (u : PowerSeries ℤ) :
    ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ u) = upL A (u.map (Int.castRingHom ↥A)) := by
  rw [ModularCurve.coeffEmb, ModularCurve.intSeriesC, coeffMap_ofPowerSeries, map_map_int, upL, map_map_int]

theorem dn_intSeries (u : PowerSeries ℤ) :
    dn A (u.map (Int.castRingHom ↥A)) = ModularCurve.intSeriesC (ResidueField ↥A) u := by
  rw [dn, map_map_int, ModularCurve.intSeriesC]

include hW hF in

theorem exists_redL_eq_of_mem_intFormRatiosC {s : LaurentSeries (ResidueField ↥A)}
    (hs : s ∈ ModularCurve.intFormRatiosC (ResidueField ↥A) Γ) : ∃ r : ↥W, redL hW r = s := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hs
  have hpg : pg.map (Int.castRingHom (ResidueField ↥A)) ≠ 0 := by
    intro h0; apply hg0; rw [ModularCurve.intSeriesC, h0, map_zero]
  have hg0Q : ModularCurve.intSeriesC ℚ pg ≠ 0 := by
    intro h0
    apply hpg
    have : pg = 0 := by
      have h1 : pg.map (Int.castRingHom ℚ) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
      exact PowerSeries.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _) (by rw [h1, map_zero])
    rw [this, map_zero]
  let r : ↥F := ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
    hF _ (ModularCurve.div_mem_qExpFunctionFieldC (Γ := Γ) f g hf hg hg0Q)⟩
  have hy : (pg.map (Int.castRingHom ↥A)).map (residue ↥A) ≠ 0 := by
    rw [map_map_int]; exact hpg
  have hpres : (r : LaurentSeries (AlgebraicClosure ℚ)) * upL A (pg.map (Int.castRingHom ↥A)) = upL A (pf.map (Int.castRingHom ↥A)) := by
    show ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) * _ = _
    rw [← coeffEmb_intSeriesC, ← coeffEmb_intSeriesC, ← map_mul, div_mul_cancel₀ _ hg0Q]
  have hr : r ∈ W := by rw [hW]; exact ⟨_, _, hy, hpres⟩
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [redL_eq_div hW ⟨r, hr⟩ hy hpres, dn_intSeries, dn_intSeries]

noncomputable def rangeField : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) where
  toSubalgebra :=
    { (redHom hW).range with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := residue_surjective c
        exact ⟨constHom A hW a, redL_constHom A hW a⟩ }
  inv_mem' := by
    rintro _ ⟨f, rfl⟩
    by_cases h0 : redL hW f = 0
    · simp only [redHom_apply, h0, inv_zero]
      exact ⟨0, redL_zero hW⟩
    · have hu : IsUnit f := by
        by_contra hnu
        exact h0 ((RingHom.mem_ker).mp (by rw [ker_redHom hW]; exact (mem_maximalIdeal _).mpr hnu))
      obtain ⟨u, rfl⟩ := hu
      refine ⟨(↑u⁻¹ : ↥W), ?_⟩
      exact eq_inv_of_mul_eq_one_left (by rw [redHom_apply, redHom_apply, ← redL_mul hW, Units.inv_mul, redL_one hW])

theorem mem_rangeField_iff {t : LaurentSeries (ResidueField ↥A)} : t ∈ rangeField A hW ↔ ∃ f : ↥W, redL hW f = t :=
  Iff.rfl

include hF in

theorem qExpFunctionFieldC_le_rangeField :
    ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ ≤ rangeField A hW := by
  rw [ModularCurve.qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
  intro s hs
  exact (mem_rangeField_iff A hW).mpr (exists_redL_eq_of_mem_intFormRatiosC A hW Γ hF hs)

end Generators
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable {F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))}
  {W : ValuationSubring ↥F} (hW : IsGaussPresented A W)
variable (jF : ↥F) (hjF : (jF : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))

include hjF in

theorem linearIndependent_of_linearIndependent_redL {m : ℕ} (v : Fin m → ↥W)
    (hli : LinearIndependent ↥(IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)})
      (fun i => redL hW (v i))) :
    LinearIndependent ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {ModularCurve.jqModC (AlgebraicClosure ℚ)})
      (fun i => (((v i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ))) := by
  classical
  set jL := ModularCurve.jqModC (AlgebraicClosure ℚ) with hjL
  set jκ := ModularCurve.jqModC (ResidueField ↥A) with hjκ
  have htL : Transcendental (AlgebraicClosure ℚ) jL := ModularCurve.transcendental_jqModC _
  have htκ : Transcendental (ResidueField ↥A) jκ := ModularCurve.transcendental_jqModC _
  have haevalL : ∀ p : Polynomial (AlgebraicClosure ℚ), aeval jL p = 0 → p = 0 := fun p hp => by
    by_contra h0; exact htL ⟨p, h0, hp⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc

  have hc' : ∀ i, ∃ r s : Polynomial (AlgebraicClosure ℚ),
      ((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {jL})) : LaurentSeries (AlgebraicClosure ℚ)) = aeval jL r / aeval jL s :=
    fun i => (IntermediateField.mem_adjoin_simple_iff (F := AlgebraicClosure ℚ) (x := _)).mp (c i).2
  choose r s hrs using hc'
  let s' : Fin m → Polynomial (AlgebraicClosure ℚ) := fun i => if s i = 0 then 1 else s i
  have hs' : ∀ i, aeval jL (s' i) ≠ 0 := by
    intro i h0
    have := haevalL _ h0
    simp only [s'] at this
    split_ifs at this with h
    · exact one_ne_zero this
    · exact h this
  let R : Fin m → Polynomial (AlgebraicClosure ℚ) := fun i =>
    if s i = 0 then 0 else r i * ∏ k ∈ Finset.univ.erase i, s' k
  let D : LaurentSeries (AlgebraicClosure ℚ) := ∏ k, aeval jL (s' k)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hs' k
  have hdc : ∀ i, aeval jL (R i) = D * ((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {jL})) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro i
    by_cases h0 : s i = 0
    · simp only [R, if_pos h0, map_zero]
      rw [hrs i, h0, map_zero, div_zero, mul_zero]
    · simp only [R, if_neg h0, map_mul, map_prod]
      rw [hrs i, show D = aeval jL (s' i) * ∏ k ∈ Finset.univ.erase i, aeval jL (s' k) from
        (Finset.mul_prod_erase Finset.univ (fun k => aeval jL (s' k)) (Finset.mem_univ i)).symm]
      simp only [s', if_neg h0]
      have hsi : aeval jL (s i) ≠ 0 := by simpa [s', h0] using hs' i
      field_simp

  suffices hR : ∀ i, R i = 0 by
    intro i
    apply Subtype.ext
    show ((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {jL})) : LaurentSeries (AlgebraicClosure ℚ)) = 0
    by_cases h0 : s i = 0
    · rw [hrs i, h0, map_zero, div_zero]
    · have := hR i
      simp only [R, if_neg h0, mul_eq_zero] at this
      rcases this with h1 | h1
      · rw [hrs i, h1, map_zero, zero_div]
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h1
        obtain ⟨k, -, hk⟩ := h1
        exact hs' k (by rw [hk, map_zero])

  have hrel : ∑ i, aeval jL (R i) * (((v i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    simp_rw [hdc, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ i, ((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {jL})) : LaurentSeries (AlgebraicClosure ℚ)) *
        (((v i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = ∑ i, c i • (((v i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ))
      from rfl, hc, mul_zero]
  by_contra hne
  push_neg at hne

  let B : ℕ := (Finset.univ.sup fun i => (R i).natDegree) + 1
  have hB : ∀ i, (R i).natDegree < B := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (R i).natDegree) (Finset.mem_univ i))
  let T : Finset (Fin m × ℕ) := (Finset.univ ×ˢ Finset.range B).filter fun ik => (R ik.1).coeff ik.2 ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    obtain ⟨k, hk⟩ : ∃ k, (R i).coeff k ≠ 0 := by
      by_contra hall; push_neg at hall; exact hi (Polynomial.ext fun k => by rw [hall k, Polynomial.coeff_zero])
    refine ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩, hk⟩⟩
    exact lt_of_le_of_lt (le_natDegree_of_ne_zero hk) (hB i)
  obtain ⟨⟨i₀, k₀⟩, hmem, hmax⟩ := T.exists_max_image (fun ik => A.valuation ((R ik.1).coeff ik.2)) hT
  set β : AlgebraicClosure ℚ := (R i₀).coeff k₀ with hβ
  have hβ0 : β ≠ 0 := (Finset.mem_filter.mp hmem).2
  have hint : ∀ i k, (R i).coeff k / β ∈ A := by
    intro i k
    by_cases h0 : (R i).coeff k = 0
    · rw [h0, zero_div]; exact zero_mem A
    · have hk : k < B := lt_of_le_of_lt (le_natDegree_of_ne_zero h0) (hB i)
      have hikT : (i, k) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hk⟩, h0⟩
      have hle := hmax (i, k) hikT
      rw [← A.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'

  let b : Fin m → ℕ → ↥A := fun i k => ⟨(R i).coeff k / β, hint i k⟩
  let jW : ↥W := ⟨jF, j_mem A hW jF hjF⟩
  let t : Fin m → ↥W := fun i => ∑ k ∈ Finset.range B, constHom A hW (b i k) * jW ^ k
  have hWcoe : ∀ x y : ↥W, (((x * y : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((x : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) * ((y : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) := fun x y => rfl
  have ht : ∀ i, (((t i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) β⁻¹ * aeval jL (R i) := by
    intro i
    rw [aeval_eq_sum_range' (hB i), Finset.mul_sum]
    simp only [t]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((R i).coeff k / β) *
        ((jF : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) ^ k = _
    rw [Algebra.smul_def, div_eq_inv_mul, map_mul, hjF, mul_assoc, map_inv₀]
  have htrel : ∑ i, t i * v i = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    show (((∑ i, t i * v i : ↥W) : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = 0
    push_cast
    simp_rw [ht, mul_assoc, ← Finset.mul_sum, hrel, mul_zero]

  have hred := congrArg (redHom hW) htrel
  rw [map_sum, map_zero] at hred
  simp only [map_mul, redHom_apply] at hred

  let P : Fin m → Polynomial (ResidueField ↥A) := fun i => ∑ k ∈ Finset.range B, monomial k (residue ↥A (b i k))
  have hP : ∀ i, redL hW (t i) = aeval jκ (P i) := by
    intro i
    simp only [t, P, map_sum]
    rw [show redL hW (∑ k ∈ Finset.range B, constHom A hW (b i k) * jW ^ k) =
        ∑ k ∈ Finset.range B, redL hW (constHom A hW (b i k) * jW ^ k) from map_sum (redHom hW) _ _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show redL hW (constHom A hW (b i k) * jW ^ k) = redL hW (constHom A hW (b i k)) * redL hW jW ^ k from by
      rw [← redHom_apply, map_mul, map_pow]; rfl]
    rw [redL_constHom, aeval_monomial]
    congr 1
    rw [show redL hW jW = jκ from redL_j A hW jF hjF]

  have hmemK : ∀ i, aeval jκ (P i) ∈ IntermediateField.adjoin (ResidueField ↥A) {jκ} := fun i =>
    IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  let γ : Fin m → ↥(IntermediateField.adjoin (ResidueField ↥A) {jκ}) := fun i => ⟨aeval jκ (P i), hmemK i⟩
  have hγrel : ∑ i, γ i • redL hW (v i) = 0 := by
    rw [← hred]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP i]
    rfl
  have hγ0 := Fintype.linearIndependent_iff.mp hli γ hγrel i₀
  have hP0 : aeval jκ (P i₀) = 0 := congrArg Subtype.val hγ0

  have hk₀ : k₀ < B := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hmem).1).2
  have hcoeff : (P i₀).coeff k₀ = 1 := by
    simp only [P, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos rfl]
      have : b i₀ k₀ = 1 := Subtype.ext (div_self hβ0)
      rw [this, map_one]
    · intro k _ hk; rw [if_neg hk]
    · intro h; exact absurd (Finset.mem_range.mpr hk₀) h
  have hPne : P i₀ ≠ 0 := fun h => by
    have := congrArg (fun q => q.coeff k₀) h
    simp only [hcoeff, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  exact htκ ⟨P i₀, hPne, hP0⟩

end Lift
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial

section PM

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_mem_sup_zpowers (H : Subgroup G) {z : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) {g : G} (hg : g ∈ H ⊔ Subgroup.zpowers z) : g ∈ H ∨ g * z ∈ H := by
  have hcomm : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  let K : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * z ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y, ← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (x * z) * (y * z) := by
            rw [mul_assoc, ← mul_assoc z, ← hcomm y, mul_assoc y, hz2, mul_one]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          have : x⁻¹ * z = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv, hcomm]
          rw [this]
          exact H.inv_mem hx }
  have hle : H ⊔ Subgroup.zpowers z ≤ K := by
    refine sup_le (fun g hg => Or.inl hg) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hz2]; exact H.one_mem)
  exact hle hg

end PM
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

theorem negOne_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem mem_or_neg_mem (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (hx : x ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    x ∈ Γ ∨ -x ∈ Γ := by
  rcases mem_or_mul_mem_of_mem_sup_zpowers Γ negOne_mem_center (by rw [neg_one_mul, neg_neg]) hx with h | h
  · exact Or.inl h
  · right; rwa [mul_neg_one] at h

section Range

variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable {F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))}
  {W : ValuationSubring ↥F} (hW : IsGaussPresented A W)
variable (jF : ↥F) (hjF : (jF : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
variable (hFQ : ∀ f : ↥F, (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)

include hT in

theorem card_le_index_of_linearIndependent {m : ℕ} (u : Fin m → LaurentSeries (AlgebraicClosure ℚ))
    (hu : ∀ i, u i ∈ ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)
    (hli : LinearIndependent ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {ModularCurve.jqModC (AlgebraicClosure ℚ)}) u) :
    m ≤ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  set Q := ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ with hQ
  have hjQ : ModularCurve.jqModC (AlgebraicClosure ℚ) ∈ Q :=
    ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC (AlgebraicClosure ℚ) Γ)
  let xQ : ↥Q := ⟨_, hjQ⟩
  obtain ⟨hfd, hle⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (AlgebraicClosure ℚ) Γ hT (Γ ⊔ Subgroup.zpowers (-1)) le_sup_left (fun γ hγ => mem_or_neg_mem Γ γ hγ) xQ rfl
  haveI := hfd
  let u' : Fin m → ↥Q := fun i => ⟨u i, hu i⟩
  have hli' : LinearIndependent ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {xQ}) u' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hmem : ∀ i, (((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {xQ})) : ↥Q) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        IntermediateField.adjoin (AlgebraicClosure ℚ) {ModularCurve.jqModC (AlgebraicClosure ℚ)} := by
      intro i
      have h := (IntermediateField.mem_lift ((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {xQ})) : ↥Q)).mpr (c i).2
      exact (IntermediateField.lift_adjoin_simple (AlgebraicClosure ℚ) Q xQ) ▸ h
    let c' : Fin m → ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {ModularCurve.jqModC (AlgebraicClosure ℚ)}) :=
      fun i => ⟨_, hmem i⟩
    have hc' : ∑ i, c' i • u i = 0 := by
      have h := congrArg (fun q : ↥Q => (q : LaurentSeries (AlgebraicClosure ℚ))) hc
      simp only [IntermediateField.coe_sum, ZeroMemClass.coe_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, IntermediateField.coe_mul]
      rfl
    have := Fintype.linearIndependent_iff.mp hli c' hc' i
    have h0 : (((c i : ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) {xQ})) : ↥Q) : LaurentSeries (AlgebraicClosure ℚ)) = 0 :=
      congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h0)
  have hcard := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  exact hcard.trans hle

end Range
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial

section RangeK

variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable {F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))}
  {W : ValuationSubring ↥F} (hW : IsGaussPresented A W)
variable (jF : ↥F) (hjF : (jF : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
variable (hF : ∀ y ∈ ModularCurve.qExpFunctionFieldC ℚ Γ, ModularCurve.coeffEmb (AlgebraicClosure ℚ) y ∈ F)
variable (hFQ : ∀ f : ↥F, (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)
variable (M : ℕ) [NeZero M] (hM : (M : ResidueField ↥A) ≠ 0)
  (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)

include hjF hT hFQ in

theorem card_le_index_of_linearIndependent_redL {m : ℕ} (e : Fin m → LaurentSeries (ResidueField ↥A))
    (he : ∀ i, e i ∈ rangeField A hW)
    (hli : LinearIndependent ↥(IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)}) e) :
    m ≤ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  choose v hv using fun i => (mem_rangeField_iff A hW).mp (he i)
  have hli' : LinearIndependent ↥(IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)})
      (fun i => redL hW (v i)) := by
    have : (fun i => redL hW (v i)) = e := funext hv
    rw [this]; exact hli
  have hL := linearIndependent_of_linearIndependent_redL A hW jF hjF v hli'
  exact card_le_index_of_linearIndependent Γ hT _ (fun i => hFQ _) hL

include hjF in
theorem adjoin_le_rangeField :
    IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)} ≤ rangeField A hW := by
  rw [IntermediateField.adjoin_simple_le_iff, mem_rangeField_iff]
  exact ⟨⟨jF, j_mem A hW jF hjF⟩, redL_j A hW jF hjF⟩

omit [Γ.FiniteIndex] in
theorem adjoin_le_qExpFunctionFieldC :
    IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)} ≤
      ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC _ Γ)

include hjF hT hF hFQ hM hΓ₁ hΓ₀ in

theorem rangeField_eq [IsAlgClosed (ResidueField ↥A)] :
    rangeField A hW = ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ := by
  classical
  set K₀ := IntermediateField.adjoin (ResidueField ↥A) {ModularCurve.jqModC (ResidueField ↥A)} with hK₀
  set Fb := ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ with hFb
  have hKE : K₀ ≤ rangeField A hW := adjoin_le_rangeField A hW jF hjF
  have hKF : K₀ ≤ Fb := adjoin_le_qExpFunctionFieldC A Γ
  have hFE : Fb ≤ rangeField A hW := qExpFunctionFieldC_le_rangeField A hW Γ hF
  let E' := IntermediateField.extendScalars hKE
  let F' := IntermediateField.extendScalars hKF
  have hle : F' ≤ E' := (IntermediateField.extendScalars_le_extendScalars_iff hKF hKE).mpr hFE

  have hrank : Module.rank ↥K₀ ↥E' ≤ ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index : ℕ) := by
    apply rank_le
    intro s hs
    let σ : Fin s.card ≃ ↥s := s.equivFin.symm
    let e : Fin s.card → LaurentSeries (ResidueField ↥A) := fun i => ((σ i : ↥s) : ↥E')
    have he : ∀ i, e i ∈ rangeField A hW := fun i => ((σ i : ↥s) : ↥E').2
    have hli : LinearIndependent ↥K₀ e := by
      have h1 := hs.comp σ σ.injective
      have h2 := h1.map' (IntermediateField.val E').toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
      exact h2
    exact card_le_index_of_linearIndependent_redL A hW jF hjF Γ hT hFQ e he hli
  haveI : Module.Finite ↥K₀ ↥E' :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _))
  have hfinE : Module.finrank ↥K₀ ↥E' ≤ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := Module.finrank_le_of_rank_le hrank

  have hjFb : ModularCurve.jqModC (ResidueField ↥A) ∈ Fb := hKF (IntermediateField.mem_adjoin_simple_self _ _)
  let x : ↥Fb := ⟨_, hjFb⟩
  have hC1 := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
    (ResidueField ↥A) M hM Γ hΓ₁ hΓ₀ x rfl
  have hfinF : Module.finrank ↥K₀ ↥F' = (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    rw [← hC1]
    symm
    have hlift : IntermediateField.lift (IntermediateField.adjoin (ResidueField ↥A) {x}) = K₀ :=
      IntermediateField.lift_adjoin_simple (ResidueField ↥A) Fb x
    let i : ↥(IntermediateField.adjoin (ResidueField ↥A) {x}) ≃+* ↥K₀ :=
      ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin (ResidueField ↥A) {x})).trans
        (IntermediateField.equivOfEq hlift)).toRingEquiv
    let j : ↥Fb ≃+* ↥F' :=
      { toFun := fun y => ⟨y.1, y.2⟩
        invFun := fun y => ⟨y.1, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    refine Algebra.finrank_eq_of_equiv_equiv i j ?_
    ext c
    rfl
  have heq : F' = E' := IntermediateField.eq_of_le_of_finrank_le hle (hfinE.trans hfinF.ge)
  apply le_antisymm _ hFE
  intro t ht
  have ht' : t ∈ E' := ht
  rw [← heq] at ht'
  exact ht'

include hjF hT hF hFQ hM hΓ₁ hΓ₀ in
theorem redL_mem [IsAlgClosed (ResidueField ↥A)] (f : ↥W) :
    redL hW f ∈ ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ := by
  rw [← rangeField_eq A hW jF hjF Γ hT hF hFQ M hM hΓ₁ hΓ₀]
  exact ⟨f, rfl⟩

noncomputable def red [IsAlgClosed (ResidueField ↥A)] :
    ↥W →+* ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ) :=
  (redHom hW).codRestrict _ (redL_mem A hW jF hjF Γ hT hF hFQ M hM hΓ₁ hΓ₀)

@[scoped simp] theorem coe_red [IsAlgClosed (ResidueField ↥A)] (f : ↥W) :
    ((red A hW jF hjF Γ hT hF hFQ M hM hΓ₁ hΓ₀ f : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) Γ)) :
      LaurentSeries (ResidueField ↥A)) = redL hW f := rfl

include hjF hT hF hFQ hM hΓ₁ hΓ₀ in
theorem red_surjective [IsAlgClosed (ResidueField ↥A)] :
    Function.Surjective (red A hW jF hjF Γ hT hF hFQ M hM hΓ₁ hΓ₀) := by
  intro t
  obtain ⟨f, hf⟩ := (mem_rangeField_iff A hW).mp (qExpFunctionFieldC_le_rangeField A hW Γ hF t.2)
  exact ⟨f, Subtype.ext hf⟩

include hjF hT hF hFQ hM hΓ₁ hΓ₀ in
theorem ker_red [IsAlgClosed (ResidueField ↥A)] :
    RingHom.ker (red A hW jF hjF Γ hT hF hFQ M hM hΓ₁ hΓ₀) = maximalIdeal ↥W := by
  rw [← ker_redHom hW]
  ext f
  simp only [RingHom.mem_ker]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

end RangeK
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial

section Fields

theorem coeffEmb_intSeriesC_eq (L : Type*) [Field L] [Algebra ℚ L] (u : PowerSeries ℤ) :
    ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ u) = ModularCurve.intSeriesC L u := by
  rw [ModularCurve.coeffEmb, ModularCurve.intSeriesC, coeffMap_ofPowerSeries, map_map_int, ModularCurve.intSeriesC]

theorem laurentBaseChange_le (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) ≤ ModularCurve.qExpFunctionFieldC L Γ := by
  rw [ModularCurve.laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩

  have hy' : y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ ModularCurve.intFormRatiosC ℚ Γ) := hy
  revert hy'
  refine fun hy' => (Subfield.closure_le (t := (ModularCurve.qExpFunctionFieldC L Γ).toSubfield.comap (ModularCurve.coeffEmb L))).mpr ?_ hy'
  rintro z (⟨r, rfl⟩ | hz)
  · show ModularCurve.coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) ∈ ModularCurve.qExpFunctionFieldC L Γ
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffEmb, ModularCurve.coeffMap_single,
      ← ModularCurve.algebraMap_laurentSeries_eq_single]
    exact IntermediateField.algebraMap_mem _ _
  · obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hz
    show ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) ∈ ModularCurve.qExpFunctionFieldC L Γ
    have hg0L : ModularCurve.intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC_eq]; intro h0; apply hg0
      exact (map_eq_zero_iff _ (ModularCurve.coeffEmb L).injective).mp h0
    rw [map_div₀, coeffEmb_intSeriesC_eq, coeffEmb_intSeriesC_eq]
    exact ModularCurve.div_mem_qExpFunctionFieldC (Γ := Γ) f g hf hg hg0L

variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

theorem gamma1_le_gammaH : CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H' := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N hA, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨A, CongruenceSubgroup.Gamma1_in_Gamma0 N hA⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact ((CongruenceSubgroup.Gamma1_mem N A).mp hA).2.1
  rw [h1]
  exact one_mem H'

theorem T_mem_Gamma1 (n : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 n := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem Gamma1_mul_le (n m : ℕ) : CongruenceSubgroup.Gamma1 (n * m) ≤ CongruenceSubgroup.Gamma1 n := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA ⊢
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := (ZMod.castHom (dvd_mul_right n m) (ZMod n)).congr_arg h1
    simpa using this
  · have := (ZMod.castHom (dvd_mul_right n m) (ZMod n)).congr_arg h2
    simpa using this
  · have := (ZMod.castHom (dvd_mul_right n m) (ZMod n)).congr_arg h3
    simpa using this

abbrev ΓT : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)

theorem gamma1_le_top : CongruenceSubgroup.Gamma1 (N * ℓ) ≤ ΓT N H' ℓ :=
  le_inf ((Gamma1_mul_le N ℓ).trans (gamma1_le_gammaH N H')) (CongruenceSubgroup.Gamma1_in_Gamma0 _)

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH N H').FiniteIndex := Subgroup.finiteIndex_of_le (gamma1_le_gammaH N H')
scoped instance finiteIndex_top : (ΓT N H' ℓ).FiniteIndex := Subgroup.finiteIndex_of_le (gamma1_le_top N H' ℓ)

theorem T_mem_gammaH : ModularGroup.T ∈ CohCarrier.GammaH N H' := gamma1_le_gammaH N H' (T_mem_Gamma1 N)
theorem T_mem_top : ModularGroup.T ∈ ΓT N H' ℓ := gamma1_le_top N H' ℓ (T_mem_Gamma1 _)

theorem jq_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.jqModC (AlgebraicClosure ℚ) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  have h : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.jqModC ℚ) = ModularCurve.jqModC (AlgebraicClosure ℚ) :=
    ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [← h]
  exact ModularCurve.coeffEmb_mem_laurentBaseChange _
    (ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))

end Fields
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial

section Assembly

noncomputable def jF (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : ↥(ModularCurve.xHFunctionFieldBar N H') :=
  ⟨ModularCurve.jqModC (AlgebraicClosure ℚ), jq_mem_laurentBaseChange (CohCarrier.GammaH N H')⟩

theorem jF_coe (N : ℕ) (H' : Subgroup (ZMod N)ˣ) :
    ((jF N H' : ↥(ModularCurve.xHFunctionFieldBar N H')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.jqModC (AlgebraicClosure ℚ) := rfl

theorem hF_bar (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : ∀ y ∈ ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H'),
    ModularCurve.coeffEmb (AlgebraicClosure ℚ) y ∈ ModularCurve.xHFunctionFieldBar N H' :=
  fun _ hy => ModularCurve.coeffEmb_mem_laurentBaseChange _ hy

theorem hFQ_bar (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : ∀ f : ↥(ModularCurve.xHFunctionFieldBar N H'),
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH N H') :=
  fun f => laurentBaseChange_le (AlgebraicClosure ℚ) (CohCarrier.GammaH N H') f.2

noncomputable def jF' (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) :
    ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ))) :=
  ⟨ModularCurve.jqModC (AlgebraicClosure ℚ), jq_mem_laurentBaseChange (ΓT N H' ℓ)⟩

theorem jF'_coe (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) :
    ((jF' N H' ℓ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)))) :
      LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) := rfl

theorem hF_top (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) : ∀ y ∈ ModularCurve.qExpFunctionFieldC ℚ (ΓT N H' ℓ),
    ModularCurve.coeffEmb (AlgebraicClosure ℚ) y ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)) :=
  fun _ hy => ModularCurve.coeffEmb_mem_laurentBaseChange _ hy

theorem hFQ_top (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) :
    ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ))),
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) (ΓT N H' ℓ) :=
  fun f => laurentBaseChange_le (AlgebraicClosure ℚ) (ΓT N H' ℓ) f.2

theorem charP_κ (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    CharP (ResidueField ↥A) p := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_
  rw [← map_natCast (residue ↥A), residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact hA

theorem hN_κ (p N : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ((N : ℕ) : ResidueField ↥A) ≠ 0 := by
  haveI := charP_κ p A hA
  rw [Ne, CharP.cast_eq_zero_iff (ResidueField ↥A) p]
  exact hpN

theorem hNℓ_κ (p N ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    (((N * ℓ : ℕ)) : ResidueField ↥A) ≠ 0 := by
  haveI := charP_κ p A hA
  rw [Ne, CharP.cast_eq_zero_iff (ResidueField ↥A) p, (Fact.out : p.Prime).dvd_mul, not_or]
  exact ⟨hpN, fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)⟩

variable (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
  (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  {W : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar N H')} (hW : IsGaussPresented A W)
  {W' : ValuationSubring ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)))}
  (hW' : IsGaussPresented A W')

noncomputable def red₁ [IsAlgClosed (ResidueField ↥A)] :
    ↥W →+* ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) :=
  red A hW (jF N H') (jF_coe N H') (CohCarrier.GammaH N H') (T_mem_gammaH N H') (hF_bar N H') (hFQ_bar N H')
    N (hN_κ p N hpN A hA) (gamma1_le_gammaH N H') (CohCarrier.GammaH_le_Gamma0 H')

noncomputable def red₂ [IsAlgClosed (ResidueField ↥A)] :
    ↥W' →+* ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) :=
  red A hW' (jF' N H' ℓ) (jF'_coe N H' ℓ) (ΓT N H' ℓ) (T_mem_top N H' ℓ) (hF_top N H' ℓ) (hFQ_top N H' ℓ)
    (N * ℓ) (hNℓ_κ p N ℓ hpN hpℓ A hA) (gamma1_le_top N H' ℓ) inf_le_right

theorem coe_red₁ [IsAlgClosed (ResidueField ↥A)] (f : ↥W) :
    ((red₁ p N H' hpN A hA hW f : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) :
      LaurentSeries (ResidueField ↥A)) = redL hW f := rfl

theorem coe_red₂ [IsAlgClosed (ResidueField ↥A)] (f : ↥W') :
    ((red₂ p N H' ℓ hpN hpℓ A hA hW' f :
      ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) :
      LaurentSeries (ResidueField ↥A)) = redL hW' f := rfl

include hW in
theorem alpha_clause [IsAlgClosed (ResidueField ↥A)] (f : ↥W) :
    ∃ h : ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W',
      red₂ p N H' ℓ hpN hpℓ A hA hW' ⟨_, h⟩ =
        ModularCurve.heckeAlphaModLH (ResidueField ↥A) N H' ℓ (red₁ p N H' hpN A hA hW f) := by
  obtain ⟨x, y, hy, hpres⟩ := exists_pres hW f
  have hpres' : ((ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) :
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)))) :
        LaurentSeries (AlgebraicClosure ℚ)) * upL A y = upL A x := by
    rw [ModularCurve.coe_heckeAlphaHBar]; exact hpres
  have h : ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W' :=
    (hW' _).mpr ⟨x, y, hy, hpres'⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  rw [ModularCurve.coe_heckeAlphaModLH, coe_red₁, coe_red₂,
    redL_eq_div hW' ⟨_, h⟩ hy hpres', redL_eq_div hW f hy hpres]

omit [NeZero N] [Fact ℓ.Prime] in
theorem upL_expand (n : ℕ) (hn : n ≠ 0) [NeZero n] (y : PowerSeries ↥A) :
    upL A (PowerSeries.expand n hn y) = ModularCurve.qExpand (AlgebraicClosure ℚ) n (upL A y) := by
  show ofPowerSeries ℤ _ _ = ModularCurve.qExpand _ n (ofPowerSeries ℤ _ _)
  rw [PowerSeries.map_expand, ModularCurve.qExpand_ofPowerSeries_eq_expand]

omit [NeZero N] [Fact ℓ.Prime] in
theorem dn_expand (n : ℕ) (hn : n ≠ 0) [NeZero n] (y : PowerSeries ↥A) :
    dn A (PowerSeries.expand n hn y) = ModularCurve.qExpand (ResidueField ↥A) n (dn A y) := by
  show ofPowerSeries ℤ _ _ = ModularCurve.qExpand _ n (ofPowerSeries ℤ _ _)
  rw [PowerSeries.map_expand, ModularCurve.qExpand_ofPowerSeries_eq_expand]

theorem expand_ne_zero {R : Type*} [CommRing R] (n : ℕ) (hn : n ≠ 0) {y : PowerSeries R} (hy : y ≠ 0) :
    PowerSeries.expand n hn y ≠ 0 := by
  intro h0
  apply hy
  ext m
  rw [← PowerSeries.coeff_expand_mul n hn y m, h0, map_zero, map_zero]

include hW in
theorem beta_clause [IsAlgClosed (ResidueField ↥A)]
    (hβ0 : ModularCurve.HeckeBetaHDefined N H' ℓ)
    (hβ : ModularCurve.HeckeBetaModLHDefined (ResidueField ↥A) N H' ℓ) (f : ↥W) :
    ∃ h : ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W',
      red₂ p N H' ℓ hpN hpℓ A hA hW' ⟨_, h⟩ =
        ModularCurve.heckeBetaModLH (ResidueField ↥A) N H' ℓ (red₁ p N H' hpN A hA hW f) := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨x, y, hy, hpres⟩ := exists_pres hW f
  have hy' : (PowerSeries.expand ℓ hℓ0 y).map (residue ↥A) ≠ 0 := by
    rw [PowerSeries.map_expand]; exact expand_ne_zero ℓ hℓ0 hy
  have hpres' : ((ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) :
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)))) :
        LaurentSeries (AlgebraicClosure ℚ)) * upL A (PowerSeries.expand ℓ hℓ0 y) = upL A (PowerSeries.expand ℓ hℓ0 x) := by
    rw [ModularCurve.coe_heckeBetaHBar _ _ _ hβ0, upL_expand, upL_expand, ← map_mul, hpres]
  have h : ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W' :=
    (hW' _).mpr ⟨_, _, hy', hpres'⟩
  refine ⟨h, ?_⟩
  apply Subtype.ext
  rw [ModularCurve.coe_heckeBetaModLH _ _ _ _ hβ, coe_red₁, coe_red₂,
    redL_eq_div hW' ⟨_, h⟩ hy' hpres', redL_eq_div hW f hy hpres, dn_expand, dn_expand, map_div₀]

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial
open scoped ModularForm

section Diamond

theorem intSeriesC_C_mul (K : Type*) [Field K] (z : ℤ) (q : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (PowerSeries.C z * q) = HahnSeries.C (z : K) * ModularCurve.intSeriesC K q := by
  rw [ModularCurve.intSeriesC, ModularCurve.intSeriesC, map_mul, PowerSeries.map_C, map_mul, ofPowerSeries_C]
  rfl

theorem isIntegralQExp_smul (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k) {pf : PowerSeries ℤ}
    (hf : ModularCurve.IsIntegralQExp f pf) (z : ℤ) :
    ModularCurve.IsIntegralQExp (⇑((z : ℂ) • f)) (PowerSeries.C z * pf) := by
  have h1 : (1 : ℝ) ∈ (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_gammaH N H')]
    exact AddSubgroup.mem_zmultiples _
  unfold ModularCurve.IsIntegralQExp at hf ⊢
  rw [ModularForm.IsGLPos.coe_smul, ModularFormClass.qExpansion_smul one_pos h1 (z : ℂ) f, map_mul, PowerSeries.map_C, hf, eq_intCast,
    PowerSeries.smul_eq_C_mul]

variable (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hpN : ¬ p ∣ N)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  {W : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar N H')} (hW : IsGaussPresented A W)

theorem gen_mem {pf pg : PowerSeries ℤ} (hmem : ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg ∈
      ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H'))
    (hpg : ModularCurve.intSeriesC (ResidueField ↥A) pg ≠ 0) :
    ∃ hr : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
        hF_bar N H' _ hmem⟩ : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W,
      redL hW ⟨_, hr⟩ = ModularCurve.intSeriesC (ResidueField ↥A) pf / ModularCurve.intSeriesC (ResidueField ↥A) pg := by
  have hpg' : pg.map (Int.castRingHom (ResidueField ↥A)) ≠ 0 := by
    intro h0; apply hpg; rw [ModularCurve.intSeriesC, h0, map_zero]
  have hg0Q : ModularCurve.intSeriesC ℚ pg ≠ 0 := by
    intro h0
    apply hpg'
    have : pg = 0 := by
      have h1 : pg.map (Int.castRingHom ℚ) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
      exact PowerSeries.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _) (by rw [h1, map_zero])
    rw [this, map_zero]
  have hy : (pg.map (Int.castRingHom ↥A)).map (residue ↥A) ≠ 0 := by
    rw [map_map_int]; exact hpg'
  have hpres : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) *
      upL A (pg.map (Int.castRingHom ↥A)) = upL A (pf.map (Int.castRingHom ↥A)) := by
    rw [← coeffEmb_intSeriesC, ← coeffEmb_intSeriesC, ← map_mul, div_mul_cancel₀ _ hg0Q]
  have hr : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
      hF_bar N H' _ hmem⟩ : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
    rw [hW]; exact ⟨_, _, hy, hpres⟩
  refine ⟨hr, ?_⟩
  rw [redL_eq_div hW ⟨_, hr⟩ hy hpres, dn_intSeries, dn_intSeries]

theorem exists_rho0 :
    ∃ ρ₀ : CongruenceSubgroup.Gamma0 N →* RingAut ↥(ModularCurve.xHFunctionField N H'),
      (∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH N H' → ρ₀ γ = 1) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) {k : ℤ}
        (f g f₁ g₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k)
        {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
        (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (_ : ModularCurve.IsIntegralQExp f₁ pf₁) (_ : ModularCurve.IsIntegralQExp g₁ pg₁)
        (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0) (_ : ModularCurve.intSeriesC ℚ pg₁ ≠ 0),
        ((ρ₀ γ ⟨ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg, ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
            ↥(ModularCurve.xHFunctionField N H')) : LaurentSeries ℚ) =
          ModularCurve.intSeriesC ℚ pf₁ / ModularCurve.intSeriesC ℚ pg₁) := by
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  letI instQ : Algebra ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H')) :=
    SubalgebraClass.toAlgebra (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H'))
  obtain ⟨ρQ, h1, -, -, h4⟩ := ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH ℚ N hN H'
  let ρ₀ : CongruenceSubgroup.Gamma0 N →* RingAut ↥(ModularCurve.xHFunctionField N H') :=
    { toFun := fun γ => (ρQ γ).toRingEquiv
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl }
  refine ⟨ρ₀, fun γ hγ => ?_, ?_⟩
  · show (ρQ γ).toRingEquiv = 1
    rw [h1 γ hγ]; rfl
  · intro γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hfs hgs hg0 hg₁0
    exact h4 γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hfs hgs hg0 hg₁0

include hpN hA in

theorem diamond_gen [IsAlgClosed (ResidueField ↥A)]
    (ρ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) ≃ₐ[ResidueField ↥A]
        ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))))
    (hρ : ModularCurve.IsDiamondPullbackModL (ResidueField ↥A) N H' ρ)
    (γ : CongruenceSubgroup.Gamma0 N) (d : (ZMod N)ˣ) (hγd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (d : ZMod N))
    {k : ℤ} (a b : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k) (pa pb : PowerSeries ℤ)
    (ha : ModularCurve.IsIntegralQExp a pa) (hb : ModularCurve.IsIntegralQExp b pb)
    (hb0 : ModularCurve.intSeriesC (ResidueField ↥A) pb ≠ 0) :
    ∃ (r : ↥W) (hr : ModularCurve.diamondAutHBar N H' d (r : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W),
      redL hW r = ModularCurve.intSeriesC (ResidueField ↥A) pa / ModularCurve.intSeriesC (ResidueField ↥A) pb ∧
      redL hW ⟨_, hr⟩ = ((ρ γ ⟨ModularCurve.intSeriesC (ResidueField ↥A) pa / ModularCurve.intSeriesC (ResidueField ↥A) pb,
          ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hb0⟩ :
        ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) : LaurentSeries (ResidueField ↥A)) := by
  classical
  haveI := charP_κ p A hA
  letI := ZMod.algebra (ResidueField ↥A) p

  have hNκ : ((N : ℕ) : ResidueField ↥A) ≠ 0 := hN_κ p N hpN A hA
  have hzp : ∀ q : PowerSeries ℤ, ModularCurve.intSeriesC (ResidueField ↥A) q ≠ 0 → ModularCurve.intSeriesC (ZMod p) q ≠ 0 := by
    intro q hq h0
    apply hq
    have h1 : q.map (Int.castRingHom (ZMod p)) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
    have h2 : q.map (Int.castRingHom (ResidueField ↥A)) = 0 := by
      rw [← RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (Int.castRingHom (ZMod p))) (Int.castRingHom _),
        ← map_map', h1, map_zero]
    rw [ModularCurve.intSeriesC, h2, map_zero]
  have hpz : ∀ q : PowerSeries ℤ, ModularCurve.intSeriesC (ZMod p) q ≠ 0 → ModularCurve.intSeriesC (ResidueField ↥A) q ≠ 0 := by
    intro q hq h0
    apply hq
    have h1 : q.map (Int.castRingHom (ResidueField ↥A)) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
    have h2 : (q.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (ResidueField ↥A)) = 0 := by
      rw [map_map', RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (Int.castRingHom (ZMod p))) (Int.castRingHom _), h1]
    have h3 : q.map (Int.castRingHom (ZMod p)) = 0 :=
      PowerSeries.map_injective _ (algebraMap (ZMod p) (ResidueField ↥A)).injective (by rw [h2, map_zero])
    rw [ModularCurve.intSeriesC, h3, map_zero]
  have hκQ : ∀ q : PowerSeries ℤ, ModularCurve.intSeriesC (ResidueField ↥A) q ≠ 0 → ModularCurve.intSeriesC ℚ q ≠ 0 := by
    intro q hq h0
    apply hq
    have : q = 0 := by
      have h1 : q.map (Int.castRingHom ℚ) = 0 := ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h0)
      exact PowerSeries.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _) (by rw [h1, map_zero])
    rw [this, ModularCurve.intSeriesC_zero]
  have hb0p := hzp pb hb0
  have hb0Q := hκQ pb hb0

  have hmem : ModularCurve.intSeriesC ℚ pa / ModularCurve.intSeriesC ℚ pb ∈ ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H') :=
    ModularCurve.div_mem_qExpFunctionFieldC (Γ := CohCarrier.GammaH N H') a b ha hb hb0Q
  obtain ⟨hr, hredr⟩ := gen_mem N H' A hW hmem hb0

  set γ' : CongruenceSubgroup.Gamma0 N := γ⁻¹ with hγ'
  have hγ'00 : (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = (d : ZMod N) := by
    rw [← hγd, hγ', Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rfl

  obtain ⟨ρp, hint, -, -, -, -⟩ := ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_zmod p N hpN H'
  obtain ⟨n, f₁, pf₁, hf₁eq, hf₁int, hf₁iff⟩ := hint γ' k a pa ha
  obtain ⟨n', g₁, pg₁, hg₁eq, hg₁int, hg₁iff⟩ := hint γ' k b pb hb

  set F₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k := (((N : ℤ) ^ n' : ℤ) : ℂ) • f₁ with hF₁
  set G₁ : ModularForm (CohCarrier.GammaH N H' : Subgroup (GL (Fin 2) ℝ)) k := (((N : ℤ) ^ n : ℤ) : ℂ) • g₁ with hG₁
  set PF₁ : PowerSeries ℤ := PowerSeries.C ((N : ℤ) ^ n') * pf₁ with hPF₁
  set PG₁ : PowerSeries ℤ := PowerSeries.C ((N : ℤ) ^ n) * pg₁ with hPG₁
  have hF₁int : ModularCurve.IsIntegralQExp F₁ PF₁ := isIntegralQExp_smul N H' f₁ hf₁int _
  have hG₁int : ModularCurve.IsIntegralQExp G₁ PG₁ := isIntegralQExp_smul N H' g₁ hg₁int _
  set c : ℂ := ((N : ℂ) ^ (n + n')) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  have hF₁eq : (⇑F₁ : UpperHalfPlane → ℂ) = c • ((⇑a : UpperHalfPlane → ℂ) ∣[k] (γ' : SL(2, ℤ))) := by
    rw [hF₁, ModularForm.IsGLPos.coe_smul, hf₁eq, smul_smul, hc]
    congr 1
    push_cast
    ring
  have hG₁eq : (⇑G₁ : UpperHalfPlane → ℂ) = c • ((⇑b : UpperHalfPlane → ℂ) ∣[k] (γ' : SL(2, ℤ))) := by
    rw [hG₁, ModularForm.IsGLPos.coe_smul, hg₁eq, smul_smul, hc]
    congr 1
    push_cast
    ring
  have hPG₁κ : ModularCurve.intSeriesC (ResidueField ↥A) PG₁ ≠ 0 := by
    rw [hPG₁, intSeriesC_C_mul]
    refine mul_ne_zero (HahnSeries.C_ne_zero ?_) (hpz pg₁ (fun h0 => hb0p (hg₁iff.mp h0)))
    push_cast
    exact pow_ne_zero _ hNκ
  have hPG₁Q : ModularCurve.intSeriesC ℚ PG₁ ≠ 0 := hκQ _ hPG₁κ

  obtain ⟨ρ₀, hρH, hρslash⟩ := exists_rho0 N H'
  have hx0 : ModularCurve.intSeriesC ℚ pa / ModularCurve.intSeriesC ℚ pb ∈ ModularCurve.xHFunctionField N H' := hmem
  have h49 := ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply N H' ρ₀ hρH
    (fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hfs hgs hg0 hg₁0 =>
      hρslash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hfs hgs hg0 hg₁0) d γ' hγ'00 ⟨_, hx0⟩
  have hval : ((ρ₀ γ' ⟨_, hx0⟩ : ↥(ModularCurve.xHFunctionField N H')) : LaurentSeries ℚ) =
      ModularCurve.intSeriesC ℚ PF₁ / ModularCurve.intSeriesC ℚ PG₁ :=
    hρslash γ' a b F₁ G₁ c hc0 ha hb hF₁int hG₁int hF₁eq hG₁eq hb0Q hPG₁Q
  rw [hval] at h49

  have hmem' : ModularCurve.intSeriesC ℚ PF₁ / ModularCurve.intSeriesC ℚ PG₁ ∈ ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H') :=
    ModularCurve.div_mem_qExpFunctionFieldC (Γ := CohCarrier.GammaH N H') F₁ G₁ hF₁int hG₁int hPG₁Q
  obtain ⟨hr', hredr'⟩ := gen_mem N H' A hW hmem' hPG₁κ
  have heq : ModularCurve.diamondAutHBar N H' d
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ pa / ModularCurve.intSeriesC ℚ pb), hF_bar N H' _ hmem⟩ :
        ↥(ModularCurve.xHFunctionFieldBar N H')) =
      ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.intSeriesC ℚ PF₁ / ModularCurve.intSeriesC ℚ PG₁), hF_bar N H' _ hmem'⟩ :=
    Subtype.ext h49
  refine ⟨⟨_, hr⟩, heq ▸ hr', hredr, ?_⟩
  rw [show (⟨_, heq ▸ hr'⟩ : ↥W) = ⟨_, hr'⟩ from Subtype.ext heq, hredr']

  symm
  have hca : ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ (n + n') : ℤ) : ℂ) • a)) (PowerSeries.C ((N : ℤ) ^ (n + n')) * pa) :=
    isIntegralQExp_smul N H' a ha _
  have hcb : ModularCurve.IsIntegralQExp (⇑((((N : ℤ) ^ (n + n') : ℤ) : ℂ) • b)) (PowerSeries.C ((N : ℤ) ^ (n + n')) * pb) :=
    isIntegralQExp_smul N H' b hb _
  have hγγ : (γ' : SL(2, ℤ)) * (γ : SL(2, ℤ)) = 1 := by rw [hγ', Subgroup.coe_inv, inv_mul_cancel]
  have hscalar : ((((N : ℤ) ^ (n + n') : ℤ)) : ℂ) = c := by rw [hc]; push_cast; ring
  have hfs : (⇑((((N : ℤ) ^ (n + n') : ℤ) : ℂ) • a) : UpperHalfPlane → ℂ) = ((⇑F₁ : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [hF₁eq, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hγγ, SlashAction.slash_one,
      ModularForm.IsGLPos.coe_smul, hscalar]
  have hgs : (⇑((((N : ℤ) ^ (n + n') : ℤ) : ℂ) • b) : UpperHalfPlane → ℂ) = ((⇑G₁ : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [hG₁eq, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, hγγ, SlashAction.slash_one,
      ModularForm.IsGLPos.coe_smul, hscalar]
  have hCκ : (HahnSeries.C ((((N : ℤ) ^ (n + n') : ℤ)) : ResidueField ↥A) : LaurentSeries (ResidueField ↥A)) ≠ 0 := by
    refine HahnSeries.C_ne_zero ?_
    push_cast
    exact pow_ne_zero _ hNκ
  have hx : (((⟨ModularCurve.intSeriesC (ResidueField ↥A) pa / ModularCurve.intSeriesC (ResidueField ↥A) pb,
          ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hb0⟩ :
        ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')))) : LaurentSeries (ResidueField ↥A)) =
      ModularCurve.intSeriesC (ResidueField ↥A) (PowerSeries.C ((N : ℤ) ^ (n + n')) * pa) /
        ModularCurve.intSeriesC (ResidueField ↥A) (PowerSeries.C ((N : ℤ) ^ (n + n')) * pb) := by
    rw [intSeriesC_C_mul, intSeriesC_C_mul, mul_div_mul_left _ _ hCκ]
  exact hρ.coe_apply_eq γ hF₁int hG₁int hca hcb hfs hgs hPG₁κ hx

end Diamond
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

namespace RedIso

open IsLocalRing HahnSeries Polynomial
open scoped ModularForm

section DiamondLift

variable (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (hpN : ¬ p ∣ N)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  {W : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar N H')} (hW : IsGaussPresented A W)

theorem ker_red₁ [IsAlgClosed (ResidueField ↥A)] : RingHom.ker (red₁ p N H' hpN A hA hW) = maximalIdeal ↥W :=
  ker_red _ _ _ _ _ _ _ _ _ _ _ _

theorem isUnit_of_red₁_ne_zero [IsAlgClosed (ResidueField ↥A)] {f : ↥W} (hf : red₁ p N H' hpN A hA hW f ≠ 0) : IsUnit f := by
  by_contra hnu
  apply hf
  exact (RingHom.mem_ker).mp (by rw [ker_red₁]; exact (mem_maximalIdeal _).mpr hnu)

theorem coe_units_inv (u : (↥W)ˣ) :
    (((↑u⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H')) = ((↑u : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H'))⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← show ((((↑u * ↑u⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H'))) =
      ((↑u : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) * ((↑u⁻¹ : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) from rfl,
    Units.mul_inv]
  rfl

include hpN hA in

theorem diamond_lift [IsAlgClosed (ResidueField ↥A)]
    (ρ : CongruenceSubgroup.Gamma0 N →*
      (↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) ≃ₐ[ResidueField ↥A]
        ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))))
    (hρ : ModularCurve.IsDiamondPullbackModL (ResidueField ↥A) N H' ρ)
    (γ : CongruenceSubgroup.Gamma0 N) (d : (ZMod N)ˣ) (hγd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (d : ZMod N))
    (x : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) :
    ∃ (f : ↥W) (h : ModularCurve.diamondAutHBar N H' d (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W),
      red₁ p N H' hpN A hA hW f = x ∧ red₁ p N H' hpN A hA hW ⟨_, h⟩ = ρ γ x := by
  classical

  let good : Set (LaurentSeries (ResidueField ↥A)) := fun t =>
    ∃ (ht : t ∈ (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) (f : ↥W) (h : (ModularCurve.diamondAutHBar N H' d) (f : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W), (red₁ p N H' hpN A hA hW) f = ⟨t, ht⟩ ∧ (red₁ p N H' hpN A hA hW) ⟨_, h⟩ = ρ γ ⟨t, ht⟩

  have hzero : (0 : LaurentSeries (ResidueField ↥A)) ∈ good := by
    have hmem0 : (ModularCurve.diamondAutHBar N H' d) ((0 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [ZeroMemClass.coe_zero, map_zero]; exact zero_mem _
    refine ⟨zero_mem _, 0, hmem0, ?_, ?_⟩
    · rw [map_zero]; rfl
    · have e : (⟨_, hmem0⟩ : ↥W) = 0 := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) ((0 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = ((0 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H'))
        rw [ZeroMemClass.coe_zero, map_zero])
      rw [e, map_zero, show (⟨(0 : LaurentSeries (ResidueField ↥A)), zero_mem (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))⟩ : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) = 0 from rfl, map_zero]
  have hone : (1 : LaurentSeries (ResidueField ↥A)) ∈ good := by
    have hmem1 : (ModularCurve.diamondAutHBar N H' d) ((1 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [OneMemClass.coe_one, map_one]; exact one_mem _
    refine ⟨one_mem _, 1, hmem1, ?_, ?_⟩
    · rw [map_one]; rfl
    · have e : (⟨_, hmem1⟩ : ↥W) = 1 := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) ((1 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = ((1 : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H'))
        rw [OneMemClass.coe_one, map_one])
      rw [e, map_one, show (⟨(1 : LaurentSeries (ResidueField ↥A)), one_mem (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))⟩ : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) = 1 from rfl, map_one]
  have hadd : ∀ {s t : LaurentSeries (ResidueField ↥A)}, s ∈ good → t ∈ good → s + t ∈ good := by
    rintro s t ⟨hs, f, hf, h1, h2⟩ ⟨ht, g, hg, h3, h4⟩
    have hmem : (ModularCurve.diamondAutHBar N H' d) ((f + g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [show ((f + g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (f : ↥(ModularCurve.xHFunctionFieldBar N H')) + g from rfl,
        map_add]
      exact add_mem hf hg
    refine ⟨add_mem hs ht, f + g, hmem, ?_, ?_⟩
    · rw [map_add, h1, h3]; rfl
    · have e : (⟨_, hmem⟩ : ↥W) = ⟨_, hf⟩ + ⟨_, hg⟩ := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) ((f + g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (ModularCurve.diamondAutHBar N H' d) f + (ModularCurve.diamondAutHBar N H' d) g
        rw [← map_add]; rfl)
      rw [e, map_add, h2, h4, ← map_add]; rfl
  have hneg : ∀ {s : LaurentSeries (ResidueField ↥A)}, s ∈ good → -s ∈ good := by
    rintro s ⟨hs, f, hf, h1, h2⟩
    have hmem : (ModularCurve.diamondAutHBar N H' d) ((-f : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [show ((-f : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = -(f : ↥(ModularCurve.xHFunctionFieldBar N H')) from rfl, map_neg]
      exact neg_mem hf
    refine ⟨neg_mem hs, -f, hmem, ?_, ?_⟩
    · rw [map_neg, h1]; rfl
    · have e : (⟨_, hmem⟩ : ↥W) = -⟨_, hf⟩ := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) ((-f : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = -(ModularCurve.diamondAutHBar N H' d) f
        rw [← map_neg]; rfl)
      rw [e, map_neg, h2, ← map_neg]; rfl
  have hmul : ∀ {s t : LaurentSeries (ResidueField ↥A)}, s ∈ good → t ∈ good → s * t ∈ good := by
    rintro s t ⟨hs, f, hf, h1, h2⟩ ⟨ht, g, hg, h3, h4⟩
    have hmem : (ModularCurve.diamondAutHBar N H' d) ((f * g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [show ((f * g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (f : ↥(ModularCurve.xHFunctionFieldBar N H')) * g from rfl,
        map_mul]
      exact mul_mem hf hg
    refine ⟨mul_mem hs ht, f * g, hmem, ?_, ?_⟩
    · rw [map_mul, h1, h3]; rfl
    · have e : (⟨_, hmem⟩ : ↥W) = ⟨_, hf⟩ * ⟨_, hg⟩ := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) ((f * g : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (ModularCurve.diamondAutHBar N H' d) f * (ModularCurve.diamondAutHBar N H' d) g
        rw [← map_mul]; rfl)
      rw [e, map_mul, h2, h4, ← map_mul]; rfl
  have hinv : ∀ {s : LaurentSeries (ResidueField ↥A)}, s ∈ good → s⁻¹ ∈ good := by
    rintro s ⟨hs, f, hf, h1, h2⟩
    by_cases hs0 : s = 0
    · simp only [hs0, inv_zero]; exact hzero
    have hRf : (red₁ p N H' hpN A hA hW) f ≠ 0 := by rw [h1]; exact fun h => hs0 (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := isUnit_of_red₁_ne_zero p N H' hpN A hA hW hRf
    have hρ0 : ρ γ ⟨s, hs⟩ ≠ 0 := by
      intro h0
      apply hs0
      have : (⟨s, hs⟩ : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) = 0 := (ρ γ).injective (by rw [h0, map_zero])
      exact congrArg Subtype.val this
    have hRDf : (red₁ p N H' hpN A hA hW) ⟨_, hf⟩ ≠ 0 := by rw [h2]; exact hρ0
    obtain ⟨u', hu'⟩ := isUnit_of_red₁_ne_zero p N H' hpN A hA hW hRDf

    have hcoe : (((↑u⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (f : ↥(ModularCurve.xHFunctionFieldBar N H'))⁻¹ := by
      rw [coe_units_inv, hu]
    have hmem : (ModularCurve.diamondAutHBar N H' d) (((↑u⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by
      rw [hcoe, map_inv₀, show (ModularCurve.diamondAutHBar N H' d) (f : ↥(ModularCurve.xHFunctionFieldBar N H')) = ((↑u' : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) from
        by rw [hu'], ← coe_units_inv]
      exact (↑u'⁻¹ : ↥W).2
    refine ⟨inv_mem hs, ↑u⁻¹, hmem, ?_, ?_⟩
    · have : (red₁ p N H' hpN A hA hW) (↑u⁻¹ : ↥W) = ((red₁ p N H' hpN A hA hW) ↑u)⁻¹ := by
        symm; apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, hu, h1]
      rfl
    · have e : (⟨_, hmem⟩ : ↥W) = ↑u'⁻¹ := Subtype.ext (by
        show (ModularCurve.diamondAutHBar N H' d) (((↑u⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (((↑u'⁻¹ : ↥W)) : ↥(ModularCurve.xHFunctionFieldBar N H'))
        rw [coe_units_inv N H' u', hu', hcoe, map_inv₀])
      have : (red₁ p N H' hpN A hA hW) (↑u'⁻¹ : ↥W) = ((red₁ p N H' hpN A hA hW) ↑u')⁻¹ := by
        symm; apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, Units.mul_inv, map_one]
      rw [e, this, hu', h2, ← map_inv₀]
      rfl
  have hconst : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c ∈ good := by
    intro c
    obtain ⟨a, rfl⟩ := residue_surjective c
    have hfix : (ModularCurve.diamondAutHBar N H' d) ((constHom A hW a : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) = (constHom A hW a : ↥W) := by
      show (ModularCurve.diamondAutHBar N H' d) (algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) = _
      rw [AlgEquiv.commutes]; rfl
    have hmem : (ModularCurve.diamondAutHBar N H' d) ((constHom A hW a : ↥W) : ↥(ModularCurve.xHFunctionFieldBar N H')) ∈ W := by rw [hfix]; exact (constHom A hW a).2
    have hval : (red₁ p N H' hpN A hA hW) (constHom A hW a) = algebraMap (ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) (residue ↥A a) :=
      Subtype.ext (show redL hW (constHom A hW a) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (residue ↥A a)
        from redL_constHom A hW a)
    refine ⟨IntermediateField.algebraMap_mem _ _, constHom A hW a, hmem, ?_, ?_⟩
    · rw [hval]; rfl
    · rw [show (⟨_, hmem⟩ : ↥W) = constHom A hW a from Subtype.ext hfix, hval,
        show (⟨algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (residue ↥A a), _⟩ : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) =
          algebraMap (ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) (residue ↥A a) from rfl, AlgEquiv.commutes]

  let S : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) :=
    { carrier := good
      mul_mem' := hmul
      one_mem' := hone
      add_mem' := hadd
      zero_mem' := hzero
      algebraMap_mem' := hconst
      inv_mem' := fun _ => hinv }

  have hgen : ModularCurve.intFormRatiosC (ResidueField ↥A) (CohCarrier.GammaH N H') ⊆ good := by
    rintro _ ⟨k, a, b, pa, pb, ha, hb, hb0, rfl⟩
    obtain ⟨r, hr, hred, hred'⟩ := diamond_gen p N H' hpN A hA hW ρ hρ γ d hγd a b pa pb ha hb hb0
    exact ⟨ModularCurve.div_mem_qExpFunctionFieldC a b ha hb hb0, r, hr, Subtype.ext (show redL hW r = _ from hred),
      Subtype.ext (show redL hW ⟨_, hr⟩ = _ from hred')⟩
  have hle : (ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H')) ≤ S := by
    rw [ModularCurve.qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    exact hgen
  obtain ⟨hx, f, h, h1, h2⟩ := hle x.2
  have ex : (⟨(x : LaurentSeries (ResidueField ↥A)), hx⟩ : ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H'))) = x := Subtype.ext rfl
  rw [ex] at h1 h2
  exact ⟨f, h, h1, h2⟩

end DiamondLift
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

end RedIso
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.RedIso"

theorem solution
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) (hℓN : ¬ ℓ ∣ N)
    (hβ0 : ModularCurve.HeckeBetaHDefined N H' ℓ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hβ : ModularCurve.HeckeBetaModLHDefined (IsLocalRing.ResidueField ↥A) N H' ℓ)
    (ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')) ≃ₐ[IsLocalRing.ResidueField ↥A]
          ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H'))))
    (hρ : ModularCurve.IsDiamondPullbackModL (IsLocalRing.ResidueField ↥A) N H' ρ)
    (W : ValuationSubring ↥(xHFunctionFieldBar N H'))
    (hW : ∀ f : ↥(xHFunctionFieldBar N H'), f ∈ W ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))))
    (W' : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))))
    (hW' : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))), f ∈ W' ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ)))) :
    ∃ (red : ↥W →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')))
      (red' : ↥W' →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))),

      (∀ (f : ↥W) (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(xHFunctionFieldBar N H')) : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H'))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (x.map (IsLocalRing.residue ↥A))) ∧
      (∀ (f : ↥W') (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red' f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (x.map (IsLocalRing.residue ↥A))) ∧

      Function.Surjective red ∧ Function.Surjective red' ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W ∧ RingHom.ker red' = IsLocalRing.maximalIdeal ↥W' ∧

      (∀ f : ↥W, ∃ h : heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H')) ∈ W',
        red' ⟨_, h⟩ = ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (red f)) ∧

      (∀ f : ↥W, ∃ h : heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H')) ∈ W',
        red' ⟨_, h⟩ = ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (red f)) ∧

      (∀ (γ : CongruenceSubgroup.Gamma0 N) (d : (ZMod N)ˣ), (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
        ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), ∃ (f : ↥W) (h : diamondAutHBar N H' d (f : ↥(xHFunctionFieldBar N H')) ∈ W),
          red f = x ∧ red ⟨_, h⟩ = ρ γ x) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hWp : RedIso.IsGaussPresented A W := hW
  have hWp' : RedIso.IsGaussPresented A W' := hW'
  refine ⟨RedIso.red₁ p N H' hpN A hA hWp, RedIso.red₂ p N H' ℓ hpN hpℓ A hA hWp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f x y hy h
    exact RedIso.redL_spec hWp f hy h
  · intro f x y hy h
    exact RedIso.redL_spec hWp' f hy h
  · exact RedIso.red_surjective _ _ _ _ _ _ _ _ _ _ _ _
  · exact RedIso.red_surjective _ _ _ _ _ _ _ _ _ _ _ _
  · exact RedIso.ker_red _ _ _ _ _ _ _ _ _ _ _ _
  · exact RedIso.ker_red _ _ _ _ _ _ _ _ _ _ _ _
  · intro f
    exact RedIso.alpha_clause p N H' ℓ hpN hpℓ A hA hWp hWp' f
  · intro f
    exact RedIso.beta_clause p N H' ℓ hpN hpℓ A hA hWp hWp' hβ0 hβ f
  · intro γ d hγd x
    exact RedIso.diamond_lift p N H' hpN A hA hWp ρ hρ γ d hγd x

end S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
end P2MW
export P2MW.S_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop (solution)
