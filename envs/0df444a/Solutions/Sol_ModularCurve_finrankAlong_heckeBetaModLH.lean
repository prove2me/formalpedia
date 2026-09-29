-- Prove2me | solution 1 for ModularCurve.finrankAlong_heckeBetaModLH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aced4eb1-1a08-51aa-9738-f73ebb76cdfa

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
import Theorems.Thm_CongruenceSubgroup_index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_heckeBetaModLH
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField
open scoped MatrixGroups

namespace DEGbeta

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
  (ℓ : ℕ) [Fact ℓ.Prime]

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem gammaH_le_gamma0 (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 M :=
  fun _ hA => (CohCarrier.mem_GammaH_iff.mp hA).1

theorem gamma1_mul_le_gamma1 (M d : ℕ) [NeZero M] [NeZero d] :
    CongruenceSubgroup.Gamma1 (M * d) ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  let r := ZMod.castHom (dvd_mul_right M d) (ZMod M)
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg r h00
    rwa [map_intCast, map_one] at this
  · have := congrArg r h11
    rwa [map_intCast, map_one] at this
  · have := congrArg r h10
    rwa [map_intCast, map_zero] at this

theorem gamma_le_gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

theorem gamma1_le_gamma0' (M : ℕ) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma0 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CongruenceSubgroup.Gamma0_mem]
  exact hA.2.2

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H'

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)

abbrev FF : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K (Gam N H')

abbrev FF' : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K (Gam' N H' ℓ)

abbrev JJ : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K {jqModC K}

abbrev φ : LaurentSeries K →ₐ[K] LaurentSeries K := qExpandAlgHomC K ℓ

abbrev JJℓ : IntermediateField K (LaurentSeries K) := (JJ K).map (φ K ℓ)

abbrev FFβ : IntermediateField K (LaurentSeries K) := (FF K N H').map (φ K ℓ)

abbrev Full : IntermediateField K (LaurentSeries K) := modularFunctionFieldFullC K ℓ

theorem j_mem_FF : jqModC K ∈ FF K N H' :=
  intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)

theorem j_mem_FF' : jqModC K ∈ FF' K N H' ℓ :=
  intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)

theorem JJ_le_FF : JJ K ≤ FF K N H' :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (j_mem_FF K N H'))

theorem JJ_le_FF' : JJ K ≤ FF' K N H' ℓ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (j_mem_FF' K N H' ℓ))

theorem FF_le_FF' : FF K N H' ≤ FF' K N H' ℓ :=
  qExpFunctionFieldC_mono K inf_le_left

theorem FFβ_le_FF' (hβ : HeckeBetaModLHDefined K N H' ℓ) : FFβ K N H' ℓ ≤ FF' K N H' ℓ := by
  rintro x ⟨y, hy, rfl⟩
  exact hβ y hy

theorem JJℓ_le_FFβ : JJℓ K ℓ ≤ FFβ K N H' ℓ :=
  IntermediateField.map_mono _ (JJ_le_FF K N H')

theorem JJ_le_Full : JJ K ≤ Full K ℓ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_full K ℓ))

theorem JJℓ_eq : JJℓ K ℓ = IntermediateField.adjoin K {qExpand K ℓ (jqModC K)} := by
  rw [JJℓ, JJ, adjoin_map, Set.image_singleton]
  rfl

theorem JJℓ_le_Full : JJℓ K ℓ ≤ Full K ℓ := by
  rw [JJℓ_eq]
  exact adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModCd_mem_full K ℓ dvd_rfl))

theorem Full_le_FF' (hβ : HeckeBetaModLHDefined K N H' ℓ) : Full K ℓ ≤ FF' K N H' ℓ := by
  rw [Full, modularFunctionFieldFullC, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hdvd with hd1 | hdl
  · subst hd1
    rw [qExpand_one_apply]
    exact j_mem_FF' K N H' ℓ
  · rw [qExpand_congr hdl]
    exact FFβ_le_FF' K N H' ℓ hβ ⟨jqModC K, j_mem_FF K N H', rfl⟩

theorem finrank_adjoin_eq_relfinrank {E : Type*} [Field E] [Algebra K E] (S : IntermediateField K E) (x : S) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set S)) S =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({(x : E)} : Set E)) S := by
  have h1 : (IntermediateField.adjoin K ({x} : Set S)).map S.val = IntermediateField.adjoin K {(x : E)} := by
    rw [adjoin_map, Set.image_singleton]; rfl
  have h2 : (⊤ : IntermediateField K S).map S.val = S := by
    rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  rw [← relfinrank_top_right, ← IntermediateField.relfinrank_map_map _ _ S.val, h1, h2]

theorem finrank_adjoin_eq_of_algEquiv {E : Type*} [Field E] [Algebra K E] (T : IntermediateField K E)
    (σ : T ≃ₐ[K] T) (a : T) :
    Module.finrank (IntermediateField.adjoin K ({a} : Set T)) T =
      Module.finrank (IntermediateField.adjoin K ({σ a} : Set T)) T := by
  have h1 : (IntermediateField.adjoin K ({a} : Set T)).map σ.toAlgHom = IntermediateField.adjoin K {σ a} := by
    rw [adjoin_map, Set.image_singleton]; rfl
  have h2 : (⊤ : IntermediateField K T).map σ.toAlgHom = ⊤ := by
    rw [← AlgHom.fieldRange_eq_map]; exact AlgHom.fieldRange_eq_top.mpr σ.surjective
  rw [← relfinrank_top_right, ← relfinrank_top_right, ← IntermediateField.relfinrank_map_map _ _ σ.toAlgHom, h1, h2]

theorem fieldRange_comp_eq_map {E : Type*} [Field E] [Algebra K E] (F F' : IntermediateField K E) (β : F →ₐ[K] F')
    (ψ : E →ₐ[K] E) (hβ : ∀ x : F, ((β x : F') : E) = ψ x) :
    (F'.val.comp β).fieldRange = F.map ψ := by
  ext y
  simp only [AlgHom.mem_fieldRange, IntermediateField.mem_map, AlgHom.comp_apply, IntermediateField.coe_val]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, x.2, (hβ x).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, hβ ⟨x, hx⟩⟩

theorem relfinrank_JJ_FF (hNK : ((N : ℕ) : K) ≠ 0) :
    relfinrank (JJ K) (FF K N H') = (Gam N H' ⊔ Subgroup.zpowers (-1)).index := by
  have h := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 K N hNK
    (Gam N H') (gamma1_le_gammaH N H') (gammaH_le_gamma0 N H') ⟨jqModC K, j_mem_FF K N H'⟩ rfl
  exact (finrank_adjoin_eq_relfinrank K (FF K N H') ⟨jqModC K, j_mem_FF K N H'⟩).symm.trans h

theorem relfinrank_JJ_FF' (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    relfinrank (JJ K) (FF' K N H' ℓ) = (Gam' N H' ℓ ⊔ Subgroup.zpowers (-1)).index := by
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hL : ((N * ℓ : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_mul]; exact mul_ne_zero hNK hℓK
  have hΓ₁ : CongruenceSubgroup.Gamma1 (N * ℓ) ≤ Gam' N H' ℓ :=
    le_inf ((gamma1_mul_le_gamma1 N ℓ).trans (gamma1_le_gammaH N H')) (gamma1_le_gamma0' (N * ℓ))
  have h := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 K (N * ℓ) hL
    (Gam' N H' ℓ) hΓ₁ inf_le_right ⟨jqModC K, j_mem_FF' K N H' ℓ⟩ rfl
  exact (finrank_adjoin_eq_relfinrank K (FF' K N H' ℓ) ⟨jqModC K, j_mem_FF' K N H' ℓ⟩).symm.trans h

theorem relfinrank_JJℓ_Full_eq (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    relfinrank (JJℓ K ℓ) (Full K ℓ) = relfinrank (JJ K) (Full K ℓ) := by
  obtain ⟨σ, hσ, -, -⟩ := ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC K ℓ hℓK
  have hJ : relfinrank (JJ K) (Full K ℓ) =
      Module.finrank (IntermediateField.adjoin K ({(⟨jqModC K, jqModC_mem_full K ℓ⟩ : ↥(Full K ℓ))} :
        Set ↥(Full K ℓ))) ↥(Full K ℓ) :=
    (finrank_adjoin_eq_relfinrank K (Full K ℓ) ⟨jqModC K, jqModC_mem_full K ℓ⟩).symm
  have hJℓ : relfinrank (JJℓ K ℓ) (Full K ℓ) =
      Module.finrank (IntermediateField.adjoin K ({(⟨jqNModC K ℓ, jqModCd_mem_full K ℓ (dvd_refl ℓ)⟩ : ↥(Full K ℓ))} :
        Set ↥(Full K ℓ))) ↥(Full K ℓ) := by
    rw [JJℓ_eq]
    exact (finrank_adjoin_eq_relfinrank K (Full K ℓ) ⟨jqNModC K ℓ, jqModCd_mem_full K ℓ (dvd_refl ℓ)⟩).symm
  rw [hJ, hJℓ, ← hσ]
  exact (finrank_adjoin_eq_of_algEquiv K (Full K ℓ) σ _).symm

theorem main (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0) (hβ : HeckeBetaModLHDefined K N H' ℓ) :
    AlgebraicCurve.finrankAlong K (heckeBetaModLH K N H' ℓ) = if ℓ ∣ N then ℓ else ℓ + 1 := by

  have hφβ : ∀ x : ↥(FF K N H'), ((heckeBetaModLH K N H' ℓ x : ↥(FF' K N H' ℓ)) : LaurentSeries K) = φ K ℓ x :=
    fun x => coe_heckeBetaModLH K N H' ℓ hβ x
  have hA : AlgebraicCurve.finrankAlong K (heckeBetaModLH K N H' ℓ) = relfinrank (FFβ K N H' ℓ) (FF' K N H' ℓ) := by
    have h0 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (FF K N H') (FF' K N H' ℓ)
      (heckeBetaModLH K N H' ℓ)
    rw [fieldRange_comp_eq_map K (FF K N H') (FF' K N H' ℓ) (heckeBetaModLH K N H' ℓ) (φ K ℓ) hφβ] at h0
    exact h0

  set d : ℕ := (Gam N H' ⊔ Subgroup.zpowers (-1)).index with hd
  set m : ℕ := (if ℓ ∣ N then ℓ else ℓ + 1) with hm
  set X : ℕ := relfinrank (FFβ K N H' ℓ) (FF' K N H' ℓ) with hX
  set r : ℕ := relfinrank (Full K ℓ) (FF' K N H' ℓ) with hr
  set t : ℕ := relfinrank (JJ K) (Full K ℓ) with ht
  have h1 : relfinrank (JJ K) (FF K N H') = d := relfinrank_JJ_FF K N H' hNK
  have h2 : relfinrank (JJ K) (FF' K N H' ℓ) = d * m := by
    rw [relfinrank_JJ_FF' K N H' ℓ hNK hℓK]
    exact CongruenceSubgroup.index_inf_gamma0_mul_sup_zpowers_neg_one_of_gamma1_le_of_le_gamma0 N (Gam N H')
      (gamma1_le_gammaH N H') (gammaH_le_gamma0 N H') ℓ Fact.out
  have h4 : relfinrank (JJℓ K ℓ) (FFβ K N H' ℓ) = d := by
    rw [← h1]; exact IntermediateField.relfinrank_map_map _ _ _
  have h5 : relfinrank (JJℓ K ℓ) (Full K ℓ) = t := relfinrank_JJℓ_Full_eq K ℓ hℓK

  have tA : relfinrank (JJℓ K ℓ) (FF' K N H' ℓ) = d * X := by
    rw [← IntermediateField.relfinrank_mul_relfinrank (JJℓ_le_FFβ K N H' ℓ) (FFβ_le_FF' K N H' ℓ hβ), h4]
  have tB : relfinrank (JJℓ K ℓ) (FF' K N H' ℓ) = t * r := by
    rw [← IntermediateField.relfinrank_mul_relfinrank (JJℓ_le_Full K ℓ) (Full_le_FF' K N H' ℓ hβ), h5]
  have tC : relfinrank (JJ K) (FF' K N H' ℓ) = t * r := by
    rw [← IntermediateField.relfinrank_mul_relfinrank (JJ_le_Full K ℓ) (Full_le_FF' K N H' ℓ hβ)]

  have hdpos : 0 < d := by
    haveI : (Gam N H' ⊔ Subgroup.zpowers (-1)).FiniteIndex :=
      Subgroup.finiteIndex_of_le
        ((gamma_le_gamma1 N).trans ((gamma1_le_gammaH N H').trans le_sup_left))
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have key : d * X = d * m := by rw [← tA, tB, ← tC, h2]
  rw [hA]
  exact Nat.eq_of_mul_eq_mul_left hdpos key

end DEGbeta

open ModularCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ) :
    AlgebraicCurve.finrankAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) =
      if ℓ ∣ N then ℓ else ℓ + 1 :=
  DEGbeta.main K N H' ℓ hNK hℓK hβ

end

end S_ModularCurve_finrankAlong_heckeBetaModLH
end P2MW
export P2MW.S_ModularCurve_finrankAlong_heckeBetaModLH (solution)
