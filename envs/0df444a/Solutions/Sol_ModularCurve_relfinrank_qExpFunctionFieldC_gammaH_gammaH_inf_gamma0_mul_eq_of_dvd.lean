-- Prove2me | solution 1 for ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/14e23cdf-0280-5b67-9b22-09d3edd975f3

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
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
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups

namespace DegAlpha

open IntermediateField

theorem finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

end DegAlpha

namespace CohCarrier
p2m_export "CohCarrier" "gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 index_gammaH_eq_index_gamma0_mul_index"
p2m_open "CohCarrier"
open CongruenceSubgroup
open scoped MatrixGroups

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

theorem gammaH_sup_zpowers_neg_one (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) =
      CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
  have hm1 : (-1 : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [Matrix.SpecialLinearGroup.coe_neg]
  have hu1 : CohCarrier.gamma0Units M ⟨-1, hm1⟩ = -1 := by
    ext; simp [CohCarrier.gamma0Units, Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
  apply le_antisymm
  · refine sup_le (ModularCurve.GammaH_mono le_sup_left) ?_
    rw [Subgroup.zpowers_le, CohCarrier.mem_GammaH_iff]
    exact ⟨hm1, by rw [hu1]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
  · intro γ hγ
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
    · exact Subgroup.mem_sup_left (CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, h⟩)
    · have hneg0 : (-γ) ∈ Gamma0 M := by
        have := Gamma0_mem.mp hγ0
        rw [Gamma0_mem]; simp [Matrix.SpecialLinearGroup.coe_neg, this]
      have hunits : CohCarrier.gamma0Units M ⟨-γ, hneg0⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ0⟩ := by
        ext; simp [CohCarrier.gamma0Units, Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
      have hnegH : (-γ) ∈ CohCarrier.GammaH M H := CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, by rw [hunits]; exact h⟩
      have e : γ = (-1) * (-γ) := by simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left hnegH)

theorem index_gammaH_sup_neg_one (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      ModularCurve.dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
  rw [gammaH_sup_zpowers_neg_one, CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index]

theorem gammaH_inf_gamma0_mul (N ℓ : ℕ) [NeZero N] [NeZero (N * ℓ)] (H' : Subgroup (ZMod N)ˣ) :
    CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ) =
      CohCarrier.GammaH (N * ℓ) (H'.comap (ZMod.unitsMap (dvd_mul_right N ℓ))) := by
  ext γ
  have hcast : ∀ z : ℤ, ZMod.castHom (dvd_mul_right N ℓ) (ZMod N) ((z : ZMod (N * ℓ))) = (z : ZMod N) :=
    fun z => map_intCast _ z
  constructor
  · rintro ⟨hH, h0⟩
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hH
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
    rw [Subgroup.mem_comap]
    convert hd using 1
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap_def, hcast]
  · intro h
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp h
    rw [Subgroup.mem_comap] at hd
    have hγ0N : γ ∈ Gamma0 N := by
      rw [Gamma0_mem] at hγ0 ⊢
      have := congrArg (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N)) hγ0
      rwa [hcast, map_zero] at this
    refine ⟨CohCarrier.mem_GammaH_iff.mpr ⟨hγ0N, ?_⟩, hγ0⟩
    convert hd using 1
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap_def, hcast]

theorem index_comap_sup_neg_one (N ℓ : ℕ) [NeZero N] [NeZero (N * ℓ)] (H' : Subgroup (ZMod N)ˣ) :
    (H'.comap (ZMod.unitsMap (dvd_mul_right N ℓ)) ⊔ Subgroup.zpowers (-1 : (ZMod (N * ℓ))ˣ)).index =
      (H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index := by
  set π := ZMod.unitsMap (dvd_mul_right N ℓ) with hπ
  have hπneg : ∀ x, π (-x) = -π x := fun x => by ext; simp [hπ, ZMod.unitsMap_def]
  have hπ1 : π (-1) = -1 := by rw [hπneg, map_one]
  have heq : H'.comap π ⊔ Subgroup.zpowers (-1 : (ZMod (N * ℓ))ˣ) = (H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).comap π := by
    apply le_antisymm
    · refine sup_le (Subgroup.comap_mono le_sup_left) ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_comap, hπ1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · intro x hx
      rw [Subgroup.mem_comap] at hx
      rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H' hx with h | h
      · exact Subgroup.mem_sup_left (Subgroup.mem_comap.mpr h)
      · have hx' : -x ∈ H'.comap π := by rw [Subgroup.mem_comap, hπneg]; exact h
        have e : x = (-1) * (-x) := by simp
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left hx')
  rw [heq]
  exact Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective (dvd_mul_right N ℓ))

end CohCarrier

open DegAlpha in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
    IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) = ℓ := by
  classical
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hℓ : ℓ.Prime := Fact.out
  have hNℓK : (((N * ℓ : ℕ)) : K) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hNK hℓK

  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' with hΓ
  set Γ' : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) with hΓ'
  have hΓ₁ : CongruenceSubgroup.Gamma1 N ≤ Γ := ModularCurve.Gamma1_le_GammaH N H'
  have hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 N := CohCarrier.GammaH_le_Gamma0 H'
  have hΓ'₁ : CongruenceSubgroup.Gamma1 (N * ℓ) ≤ Γ' := by
    refine le_inf ((ModularCurve.Gamma1_le_of_dvd (dvd_mul_right N ℓ)).trans hΓ₁) ?_
    exact (ModularCurve.Gamma1_le_GammaH (N * ℓ) ⊥).trans (CohCarrier.GammaH_le_Gamma0 ⊥)
  have hΓ'₀ : Γ' ≤ CongruenceSubgroup.Gamma0 (N * ℓ) := inf_le_right
  have hΓ'Γ : Γ' ≤ Γ := inf_le_left

  set F := ModularCurve.qExpFunctionFieldC K Γ with hF
  set F' := ModularCurve.qExpFunctionFieldC K Γ' with hF'
  have hFF' : F ≤ F' := ModularCurve.qExpFunctionFieldC_mono K hΓ'Γ
  have hjF : ModularCurve.jqModC K ∈ F := ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _)
  have hjF' : ModularCurve.jqModC K ∈ F' := hFF' hjF

  have e1 := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 K N hNK Γ hΓ₁ hΓ₀
    ⟨ModularCurve.jqModC K, hjF⟩ rfl
  have e2 := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 K (N * ℓ) hNℓK Γ' hΓ'₁ hΓ'₀
    ⟨ModularCurve.jqModC K, hjF'⟩ rfl
  set A : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K)) with hA
  have hAF : A ≤ F := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjF)
  have r1 : A.relfinrank F = (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    rw [hA, ← finrank_adjoin_eq_relfinrank F ⟨ModularCurve.jqModC K, hjF⟩]; exact e1
  have r2 : A.relfinrank F' = (Γ' ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    rw [hA, ← finrank_adjoin_eq_relfinrank F' ⟨ModularCurve.jqModC K, hjF'⟩]; exact e2

  have i1 : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      ModularCurve.dedekindPsi N * (H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index :=
    CohCarrier.index_gammaH_sup_neg_one N H'
  have i2 : (Γ' ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      ℓ * (ModularCurve.dedekindPsi N * (H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index) := by
    rw [hΓ', CohCarrier.gammaH_inf_gamma0_mul, CohCarrier.index_gammaH_sup_neg_one, CohCarrier.index_comap_sup_neg_one,
      ModularCurve.dedekindPsi_mul_prime N ℓ hℓ, if_pos hℓN, mul_assoc]
  have hpos : 0 < (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    haveI : (CongruenceSubgroup.Gamma1 N).FiniteIndex := (CongruenceSubgroup.Gamma1_is_congruence N).finiteIndex
    haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
    haveI : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have t := IntermediateField.relfinrank_mul_relfinrank hAF hFF'
  rw [r1, r2, i2, i1] at t

  rw [i1] at hpos
  have := Nat.eq_of_mul_eq_mul_left hpos (t.trans (mul_comm _ _))
  exact this

end S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
end P2MW
export P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd (solution)
