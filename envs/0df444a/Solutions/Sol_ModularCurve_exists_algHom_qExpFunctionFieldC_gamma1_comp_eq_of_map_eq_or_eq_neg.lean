-- Prove2me | solution 1 for ModularCurve.exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b8c991c6-88e6-58c4-aa26-dcc77bdd2a89

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_XH
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve WeierstrassCurve~cusp WeierstrassCurve.Affine Polynomial"
open scoped MatrixGroups

noncomputable section

namespace P2MKcKron

universe u v w

theorem exists_pointEquiv_of_smul_eq {F : Type u} [Field F] [DecidableEq F] (C : VariableChange F)
    (W V : WeierstrassCurve F) (h : C • W = V) :
    ∃ e : V.toAffine.Point ≃+ W.toAffine.Point,
      ∀ (x y : F) (hxy : V.toAffine.Nonsingular x y),
        ∃ h' : W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t),
          e (.some x y hxy) = .some ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) h' := by
  subst h
  let e₀ : (C • W).toAffine.Point ≃ W.toAffine.Point := Point.variableChangeEquiv C W
  have hinv : ∀ P Q : W.toAffine.Point, e₀.symm (P + Q) = e₀.symm P + e₀.symm Q :=
    fun P Q => Point.vcInvFun_add C W P Q
  let eI : W.toAffine.Point ≃+ (C • W).toAffine.Point := AddEquiv.mk' e₀.symm hinv
  refine ⟨eI.symm, fun x y hxy => ?_⟩
  refine ⟨(nonsingular_variableChange_iff x y).mp hxy, ?_⟩
  show e₀ (.some x y hxy) = _
  rfl

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [DecidableEq Ω] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : Ω) ≠ 0) :
    Nat.card {Q : (E.baseChange Ω).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem ne_of_transcendental {R A : Type*} [Field R] [Field A] [Algebra R A] {a : A}
    (ha : Transcendental R a) (n : ℕ) : a ≠ (n : A) := by
  intro h
  apply ha
  rw [h, show ((n : A)) = algebraMap R A n by simp]
  exact isAlgebraic_algebraMap _

theorem c₄_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₄ ≠ 0 := by
  intro h
  have : W.j = 0 := W.j_eq_zero h
  exact ne_of_transcendental hW 0 (by rw [this, Nat.cast_zero])

theorem c₆_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₆ ≠ 0 := by
  intro h
  have hrel := W.c_relation
  rw [h, zero_pow two_ne_zero, sub_zero] at hrel
  have : W.j = 1728 := by
    rw [WeierstrassCurve.j, ← hrel, ← W.coe_Δ', mul_left_comm, Units.inv_mul, mul_one]
  exact ne_of_transcendental hW 1728 (by rw [this]; norm_num)

theorem exists_algHom_apply_eq {K k F : Type*} [Field K] [Field k] [Field F] [Algebra K k]
    [Algebra K F] (t : k) (ht : Transcendental K t)
    (hgen : IntermediateField.adjoin K ({t} : Set k) = ⊤) (y : F) (hy : Transcendental K y) :
    ∃ ι : k →ₐ[K] F, ι t = y := by
  have hinjF : Function.Injective (Polynomial.aeval y : K[X] →ₐ[K] F) :=
    transcendental_iff_injective.1 hy
  have hinjk : Function.Injective (Polynomial.aeval t : K[X] →ₐ[K] k) :=
    transcendental_iff_injective.1 ht
  let iF : RatFunc K →ₐ[K] F := IsFractionRing.liftAlgHom hinjF
  let ik : RatFunc K →ₐ[K] k := IsFractionRing.liftAlgHom hinjk
  have hikX : ik (algebraMap K[X] (RatFunc K) X) = t := by
    change IsFractionRing.lift hinjk (algebraMap K[X] (RatFunc K) X) = t
    rw [IsFractionRing.lift_algebraMap]
    change Polynomial.aeval t (X : K[X]) = t
    exact Polynomial.aeval_X t
  have hiFX : iF (algebraMap K[X] (RatFunc K) X) = y := by
    change IsFractionRing.lift hinjF (algebraMap K[X] (RatFunc K) X) = y
    rw [IsFractionRing.lift_algebraMap]
    change Polynomial.aeval y (X : K[X]) = y
    exact Polynomial.aeval_X y
  have hsurj : Function.Surjective ik := by
    intro z
    have hz : z ∈ (⊤ : IntermediateField K k) := IntermediateField.mem_top
    rw [← hgen] at hz
    have hle : IntermediateField.adjoin K ({t} : Set k) ≤ ik.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact ⟨_, hikX⟩
    obtain ⟨w, hw⟩ := AlgHom.mem_fieldRange.1 (hle hz)
    exact ⟨w, hw⟩
  let e : RatFunc K ≃ₐ[K] k := AlgEquiv.ofBijective ik ⟨ik.toRingHom.injective, hsurj⟩
  refine ⟨iF.comp (e.symm : k →ₐ[K] RatFunc K), ?_⟩
  change iF (e.symm t) = y
  have : e.symm t = algebraMap K[X] (RatFunc K) X := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact hikX.symm
  rw [this, hiFX]

theorem le_of_index_le {G : Type*} [Group G] {H K : Subgroup G} (hle : K ≤ H)
    (hidx : K.index ≤ H.index) (hK : K.index ≠ 0) : H ≤ K := by
  have hmul := Subgroup.relIndex_mul_index hle
  have hH : H.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact hK hmul.symm
  have hrel_le : K.relIndex H ≤ 1 := by
    have : K.relIndex H * H.index ≤ 1 * H.index := by rw [hmul, one_mul]; exact hidx
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hH)
  have hrel_ne : K.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hK hmul.symm
  have hrel : K.relIndex H = 1 := by omega
  exact Subgroup.relIndex_eq_one.1 hrel

section Count

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

def eqLocus (ψ ψ₀ : F →ₐ[K] Ω) : IntermediateField K F where
  carrier := {y | ψ y = ψ₀ y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, map_add, ha, hb]
  zero_mem' := by simp
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    rw [AlgHom.commutes, AlgHom.commutes]
  inv_mem' a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]

theorem apply_eq_of_mem_adjoin {ψ ψ₀ : F →ₐ[K] Ω} {x : F} (hx : ψ x = ψ₀ x) {y : F}
    (hy : y ∈ IntermediateField.adjoin K ({x} : Set F)) : ψ y = ψ₀ y := by
  have hle : IntermediateField.adjoin K ({x} : Set F) ≤ eqLocus ψ ψ₀ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hle hy

theorem finite_and_natCard_le_of_mk_le {X : Type*} {n : ℕ} (h : Cardinal.mk X ≤ n) :
    Finite X ∧ Nat.card X ≤ n := by
  have hfin : Cardinal.mk X < Cardinal.aleph0 := lt_of_le_of_lt h Cardinal.natCast_lt_aleph0
  haveI : Finite X := Cardinal.lt_aleph0_iff_finite.mp hfin
  refine ⟨this, ?_⟩
  have := Cardinal.toNat_le_toNat h Cardinal.natCast_lt_aleph0
  first | exact this | simpa [Nat.card] using this

theorem finite_and_natCard_algHom_le (L F Ω : Type*) [Field L] [Field F] [Field Ω] [Algebra L F]
    [Algebra L Ω] [FiniteDimensional L F] :
    Finite (F →ₐ[L] Ω) ∧ Nat.card (F →ₐ[L] Ω) ≤ Module.finrank L F := by
  have h := cardinalMk_algHom L F Ω
  rw [Module.finrank_linearMap_self L Ω F] at h
  exact finite_and_natCard_le_of_mk_le h

theorem finite_and_natCard_normalised_le (x : F) (c : Ω)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Finite {ψ : F →ₐ[K] Ω // ψ x = c} ∧
      Nat.card {ψ : F →ₐ[K] Ω // ψ x = c} ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  by_cases hne : Nonempty {ψ : F →ₐ[K] Ω // ψ x = c}
  swap
  · rw [not_nonempty_iff] at hne
    exact ⟨Finite.of_subsingleton, by simp⟩
  obtain ⟨⟨ψ₀, hψ₀⟩⟩ := hne
  set L := IntermediateField.adjoin K ({x} : Set F) with hL
  letI : Algebra L Ω := ((ψ₀ : F →+* Ω).comp (algebraMap L F)).toAlgebra
  let ι : {ψ : F →ₐ[K] Ω // ψ x = c} → (F →ₐ[L] Ω) := fun ψ =>
    { (ψ.1 : F →+* Ω) with
      commutes' := fun r => by
        show ψ.1 (r : F) = ψ₀ (r : F)
        exact apply_eq_of_mem_adjoin (ψ.2.trans hψ₀.symm) r.2 }
  have hι : Function.Injective ι := by
    intro ψ ψ' h
    apply Subtype.ext
    apply AlgHom.ext
    intro y
    exact congrArg (fun φ : F →ₐ[L] Ω => φ y) h
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_algHom_le L F Ω
  haveI := hfin
  exact ⟨Finite.of_injective ι hι, (Nat.card_le_card_of_injective ι hι).trans hcard⟩

end Count

section EmbAction

variable (K k Ω A : Type*) [Field K] [Field k] [Field Ω] [Field A] [Algebra K k] [Algebra K Ω]
  [Algebra k Ω] [IsScalarTower K k Ω] [Algebra K A]

@[reducible] def embAction : MulAction (Ω ≃ₐ[k] Ω) (A →ₐ[K] Ω) where
  smul σ ψ := ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ
  one_smul ψ := by
    apply AlgHom.ext
    intro a
    rfl
  mul_smul σ τ ψ := by
    apply AlgHom.ext
    intro a
    rfl

attribute [local instance] embAction

variable {K k Ω A}

theorem emb_smul_def (σ : Ω ≃ₐ[k] Ω) (ψ : A →ₐ[K] Ω) :
    σ • ψ = ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ := rfl

theorem emb_smul_apply (σ : Ω ≃ₐ[k] Ω) (ψ : A →ₐ[K] Ω) (a : A) : (σ • ψ) a = σ (ψ a) := rfl

end EmbAction

section Cls

variable {G Pt : Type*} [Group G] [AddCommGroup Pt] [DistribMulAction G Pt] (M : ℕ) [NeZero M]

abbrev orbb (P : Pt) : Set Pt :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1) ∧
    T = (u : ZMod M).val • P}

abbrev Cls (Pt : Type*) [AddCommGroup Pt] (M : ℕ) : Type _ :=
  {s : Set Pt // ∃ P : Pt, addOrderOf P = M ∧ s = orbb M P}

theorem nsmul_eq_mod_nsmul {P : Pt} (hP : M • P = 0) (n : ℕ) : n • P = (n % M) • P := by
  conv_lhs => rw [← Nat.mod_add_div n M, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

theorem val_natCast_nsmul {P : Pt} (hP : M • P = 0) (n : ℕ) : ((n : ZMod M).val) • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul M hP]

theorem val_add_nsmul {P : Pt} (hP : M • P = 0) (u v : ZMod M) :
    (u + v).val • P = u.val • P + v.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul M hP, add_nsmul]

theorem val_neg_nsmul {P : Pt} (hP : M • P = 0) (u : ZMod M) : (-u).val • P = -(u.val • P) := by
  have h : (-u + u).val • P = 0 := by rw [neg_add_cancel, ZMod.val_zero, zero_nsmul]
  rw [val_add_nsmul M hP] at h
  exact eq_neg_of_add_eq_zero_left h

theorem val_one_nsmul {P : Pt} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul M hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem val_neg_one_nsmul {P : Pt} (hP : M • P = 0) : (-1 : ZMod M).val • P = -P := by
  rw [val_neg_nsmul M hP, val_one_nsmul M hP]

theorem nsmul_of_addOrderOf_eq {P : Pt} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem eq_or_eq_of_mem_zpowers_neg_one {b : (ZMod M)ˣ}
    (hb : b ∈ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : b = 1 ∨ b = -1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd n with hn | hn
  · exact Or.inl hn.neg_one_zpow
  · exact Or.inr hn.neg_one_zpow

theorem eq_or_eq_of_mem_bot_sup {u : (ZMod M)ˣ}
    (hu : u ∈ (⊥ : Subgroup (ZMod M)ˣ) ⊔ Subgroup.zpowers (-1)) : u = 1 ∨ u = -1 := by
  rw [bot_sup_eq] at hu
  exact eq_or_eq_of_mem_zpowers_neg_one M hu

theorem mem_orbb_iff {P : Pt} (hP : M • P = 0) (T : Pt) : T ∈ orbb M P ↔ T = P ∨ T = -P := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases eq_or_eq_of_mem_bot_sup M hu with rfl | rfl
    · exact Or.inl (by rw [Units.val_one, val_one_nsmul M hP])
    · exact Or.inr (by rw [Units.val_neg, Units.val_one, val_neg_one_nsmul M hP])
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul M hP]⟩
    · exact ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
        by rw [Units.val_neg, Units.val_one, val_neg_one_nsmul M hP]⟩

theorem orbb_neg {P : Pt} (hP : M • P = 0) : orbb M (-P) = orbb M P := by
  ext T
  rw [mem_orbb_iff M hP, mem_orbb_iff M (by rw [smul_neg, hP, neg_zero]), neg_neg, or_comm]

theorem orbb_eq_orbb_iff {P Q : Pt} (hP : M • P = 0) (hQ : M • Q = 0) :
    orbb M Q = orbb M P ↔ Q = P ∨ Q = -P := by
  constructor
  · intro h
    have hQmem : Q ∈ orbb M Q := (mem_orbb_iff M hQ Q).2 (Or.inl rfl)
    rw [h] at hQmem
    exact (mem_orbb_iff M hP Q).1 hQmem
  · rintro (rfl | rfl)
    · rfl
    · exact orbb_neg M hP

theorem image_orbb {B : Type*} [AddCommGroup B] (m : Pt →+ B) (P : Pt) :
    m '' orbb M P = orbb M (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

theorem image_smul_orbb (g : G) (P : Pt) :
    (fun T : Pt => g • T) '' orbb M P = orbb M (g • P) :=
  image_orbb M (DistribSMul.toAddMonoidHom Pt g) P

theorem addOrderOf_smul_eq (g : G) {P : Pt} (hP : addOrderOf P = M) : addOrderOf (g • P) = M := by
  have hinj : Function.Injective (DistribSMul.toAddMonoidHom Pt g) := fun a b h =>
    smul_left_cancel g h
  have := addOrderOf_injective (DistribSMul.toAddMonoidHom Pt g) hinj P
  rw [DistribSMul.toAddMonoidHom_apply] at this
  rw [this, hP]

variable (G Pt) in

@[reducible] def clsAction : MulAction G (Cls Pt M) where
  smul g s := ⟨(fun T : Pt => g • T) '' s.1, by
    obtain ⟨P, hP, hs⟩ := s.2
    exact ⟨g • P, addOrderOf_smul_eq M g hP, by rw [hs, image_smul_orbb]⟩⟩
  one_smul s := by
    apply Subtype.ext
    show (fun T : Pt => (1 : G) • T) '' s.1 = s.1
    have : (fun T : Pt => (1 : G) • T) = id := funext fun T => one_smul G T
    rw [this, Set.image_id]
  mul_smul g h s := by
    apply Subtype.ext
    show (fun T : Pt => (g * h) • T) '' s.1 = (fun T : Pt => g • T) '' ((fun T : Pt => h • T) '' s.1)
    rw [Set.image_image]
    exact Set.image_congr fun T _ => mul_smul g h T

attribute [local instance] clsAction

theorem cls_smul_val (g : G) (s : Cls Pt M) : (g • s).1 = (fun T : Pt => g • T) '' s.1 := rfl

theorem smul_cls_eq_iff (g : G) (s : Cls Pt M) {P : Pt} (hP : addOrderOf P = M)
    (hs : s.1 = orbb M P) : g • s = s ↔ g • P = P ∨ g • P = -P := by
  have hP0 : M • P = 0 := nsmul_of_addOrderOf_eq M hP
  have hgP0 : M • (g • P) = 0 := by rw [smul_comm, hP0, smul_zero]
  rw [← Subtype.coe_inj, cls_smul_val, hs, image_smul_orbb]
  exact orbb_eq_orbb_iff M hP0 hgP0

theorem orbit_cls_eq_univ
    (htrans : ∀ P P' : Pt, addOrderOf P = M → addOrderOf P' = M → ∃ g : G, P' = g • P)
    (s : Cls Pt M) : MulAction.orbit G s = Set.univ := by
  apply Set.eq_univ_of_forall
  intro s'
  obtain ⟨P, hP, hs⟩ := s.2
  obtain ⟨P', hP', hs'⟩ := s'.2
  obtain ⟨g, rfl⟩ := htrans P P' hP hP'
  refine ⟨g, ?_⟩
  apply Subtype.ext
  show (fun T : Pt => g • T) '' s.1 = s'.1
  rw [hs, hs', image_smul_orbb]

theorem index_stabilizer_cls
    (htrans : ∀ P P' : Pt, addOrderOf P = M → addOrderOf P' = M → ∃ g : G, P' = g • P)
    (s : Cls Pt M) : (MulAction.stabilizer G s).index = Nat.card (Cls Pt M) := by
  rw [MulAction.index_stabilizer, orbit_cls_eq_univ M htrans s, Set.ncard_univ]

end Cls

theorem tateLaurent_a₁ (K : Type*) [CommRing K] : (tateLaurent K).a₁ = 1 := by
  simp [tateLaurent]

theorem tateLaurent_a₂ (K : Type*) [CommRing K] : (tateLaurent K).a₂ = 0 := by
  simp [tateLaurent]

theorem tateLaurent_a₃ (K : Type*) [CommRing K] : (tateLaurent K).a₃ = 0 := by
  simp [tateLaurent]

theorem tateLaurent_b₂ (K : Type*) [CommRing K] : (tateLaurent K).b₂ = 1 := by
  simp [WeierstrassCurve.b₂, tateLaurent_a₁, tateLaurent_a₂]

theorem tateLaurent_b₄ (K : Type*) [CommRing K] : (tateLaurent K).b₄ = 2 * (tateLaurent K).a₄ := by
  simp [WeierstrassCurve.b₄, tateLaurent_a₁, tateLaurent_a₃]

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem Gamma1_one_eq_top : CongruenceSubgroup.Gamma1 1 = ⊤ := by
  refine eq_top_iff.2 fun A _ => ?_
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem SL_mem_zpowers_neg_one_iff (n : SL(2, ℤ)) :
    n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ n = 1 ∨ n = -1 := by
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_or_neg_mem_of_mem_sup (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h : σ ∈ Γ ⊔ Subgroup.zpowers (-1)) : σ ∈ Γ ∨ -σ ∈ Γ := by
  have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
  rw [Subgroup.mul_normal] at h'
  obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · exact Or.inl (by simpa using hγ)
  · exact Or.inr (by simpa using hγ)

theorem mem_range_of_eval₂_eq_zero {R L : Type*} [Field R] [Field L] [IsAlgClosed R] (i : R →+* L)
    (q : Polynomial R) (hq : q ≠ 0) (z : L) (hz : q.eval₂ i z = 0) : z ∈ Set.range i := by
  classical
  have hmem : z ∈ (q.map i).roots := (Polynomial.mem_roots_map_of_injective i.injective hq).2 hz
  rw [(IsAlgClosed.splits q).roots_map i, Multiset.mem_map] at hmem
  obtain ⟨a, -, rfl⟩ := hmem
  exact ⟨a, rfl⟩

theorem exists_eq_some_of_ne_zero {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R}
    (P : W.Point) (h : P ≠ 0) : ∃ (a b : R) (hab : W.Nonsingular a b), P = .some a b hab := by
  cases P with
  | zero => exact absurd rfl h
  | some a b hab => exact ⟨a, b, hab, rfl⟩

section Main

attribute [local instance] embAction clsAction

variable (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)

local notation "Fb" => qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)

variable
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)

@[reducible] def ptAction :
    DistribMulAction (Ω ≃ₐ[k] Ω) (E.baseChange Ω).toAffine.Point where
  smul σ P := Point.map (σ : Ω →ₐ[k] Ω) P
  one_smul P := by
    show Point.map _ P = P
    cases P <;> rfl
  mul_smul σ τ P := by
    show Point.map _ P = Point.map _ (Point.map _ P)
    cases P <;> rfl
  smul_zero σ := by
    show Point.map _ 0 = 0
    rfl
  smul_add σ P Q := by
    show Point.map _ (P + Q) = Point.map _ P + Point.map _ Q
    exact map_add _ P Q

attribute [local instance] ptAction

theorem pt_smul_def (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    σ • P = Point.map (σ : Ω →ₐ[k] Ω) P := rfl

include hM hx hE hgen in
theorem main :
    ∃ (P₀ : (E.baseChange Ω).toAffine.Point)
      (ψ₀ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω),
      addOrderOf P₀ = M ∧ ψ₀ x = algebraMap k Ω E.j ∧
      ∀ σ : Ω ≃ₐ[k] Ω,
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨
          WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) →
        ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ := by
  classical

  let F : Type u := LaurentSeries K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hMΩ : (M : Ω) ≠ 0 := fun h =>
    hM ((algebraMap K Ω).injective (by rw [map_natCast, map_zero]; exact h))
  have hyt : Transcendental K (jqModC K) := transcendental_jqModC K
  obtain ⟨ι, hιj⟩ := exists_algHom_apply_eq E.j hE hgen (jqModC K : F) hyt
  let L := AlgebraicClosure F
  let ιL : k →+* L := (algebraMap F L).comp (ι : k →+* F)
  letI : Algebra k L := ιL.toAlgebra
  have hιL : ∀ z : k, algebraMap k L z = algebraMap F L (ι z) := fun z => rfl
  haveI : IsScalarTower K k L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [hιL, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hML : (M : L) ≠ 0 := fun h =>
    hM ((algebraMap K L).injective (by rw [map_natCast, map_zero]; exact h))

  let ιΩ : Ω →ₐ[k] L := IsAlgClosed.lift
  let ιΩK : Ω →ₐ[K] L := ιΩ.restrictScalars K
  have hιΩK : ∀ z, ιΩK z = ιΩ z := fun z => rfl
  have hιΩKinj : Function.Injective ιΩK := ιΩ.toRingHom.injective

  let θ : Fb →ₐ[K] L := (IsScalarTower.toAlgHom K F L).comp (IntermediateField.val Fb)
  have hθ : ∀ g : Fb, θ g = algebraMap F L (g : F) := fun g => rfl
  have hθx : θ x = ιΩK (algebraMap k Ω E.j) := by
    rw [hθ, hx, hιΩK, AlgHom.commutes, hιL, hιj]

  set Kx := IntermediateField.adjoin K ({x} : Set Fb) with hKx
  obtain ⟨hfinU, hdegU⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CongruenceSubgroup.Gamma1 M) (T_mem_Gamma1 M)
      (CohCarrier.GammaH M ⊥ ⊔ Subgroup.zpowers (-1))
      (by rw [ModularCurve.GammaH_bot]; exact le_sup_left)
      (fun γ hγ => by
        have := mem_or_neg_mem_of_mem_sup (CohCarrier.GammaH M ⊥) γ hγ
        rwa [ModularCurve.GammaH_bot] at this)
      x hx
  haveI := hfinU
  have hrangeθ : ∀ f : Fb, θ f ∈ ιΩK.range := by
    intro f
    have hint : IsIntegral Kx f := Algebra.IsIntegral.isIntegral f
    let φ : Kx →+* L := θ.toRingHom.comp (algebraMap Kx Fb)
    have hφroot : ((minpoly Kx f).map φ).eval (θ f) = 0 := by
      rw [Polynomial.eval_map]
      change Polynomial.eval₂ (θ.toRingHom.comp (algebraMap Kx Fb)) (θ.toRingHom f) (minpoly Kx f) = 0
      rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

    have hφΩ : ∀ z : Kx, φ z ∈ Set.range ιΩK := by
      let T : IntermediateField K Fb := IntermediateField.comap θ ιΩK.fieldRange
      have hle : Kx ≤ T := by
        rw [hKx, IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        change θ x ∈ ιΩK.fieldRange
        rw [hθx]
        exact ⟨_, rfl⟩
      intro z
      have hz : (z : Fb) ∈ T := hle z.2
      change θ z ∈ ιΩK.fieldRange at hz
      obtain ⟨w, hw⟩ := AlgHom.mem_fieldRange.1 hz
      exact ⟨w, hw⟩
    have hlift : (minpoly Kx f).map φ ∈ Polynomial.lifts (ιΩK : Ω →+* L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hφΩ _
    obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 hlift
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hq
      exact (Polynomial.map_ne_zero (minpoly.ne_zero hint)) hq.symm
    have hqroot : q.eval₂ (ιΩK : Ω →+* L) (θ f) = 0 := by
      rw [← Polynomial.eval_map, hq]; exact hφroot
    obtain ⟨z, hz⟩ := mem_range_of_eval₂_eq_zero (ιΩK : Ω →+* L) q hq0 (θ f) hqroot
    exact ⟨z, hz⟩

  let eΩ : Ω ≃ₐ[K] ιΩK.range := AlgEquiv.ofInjective ιΩK hιΩKinj
  have heΩ : ∀ z : ιΩK.range, ιΩK (eΩ.symm z) = (z : L) := fun z => by
    rw [← AlgEquiv.ofInjective_apply ιΩK hιΩKinj]; simp [eΩ]
  let ψ₀ : Fb →ₐ[K] Ω := (eΩ.symm : ιΩK.range →ₐ[K] Ω).comp (θ.codRestrict ιΩK.range hrangeθ)
  have hψ₀ : ∀ f : Fb, ιΩK (ψ₀ f) = θ f := by
    intro f
    change ιΩK (eΩ.symm _) = _
    rw [heΩ]
    rfl
  have hψ₀x : ψ₀ x = algebraMap k Ω E.j := by
    apply hιΩKinj
    rw [hψ₀, hθx]

  set G := (Ω ≃ₐ[k] Ω) with hGdef
  have hstabψ : ∀ σ : Ω ≃ₐ[k] Ω,
      σ ∈ MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀ ↔ ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ :=
    fun σ => Iff.rfl

  have horb_sub : MulAction.orbit (Ω ≃ₐ[k] Ω) ψ₀ ⊆ {ψ : Fb →ₐ[K] Ω | ψ x = algebraMap k Ω E.j} := by
    rintro ψ ⟨σ, rfl⟩
    show (σ • ψ₀) x = algebraMap k Ω E.j
    rw [emb_smul_apply, hψ₀x, AlgEquiv.commutes]
  obtain ⟨hfinNE, hcardNE⟩ := finite_and_natCard_normalised_le (K := K) (Ω := Ω) x (algebraMap k Ω E.j)
  have hNEfin : ({ψ : Fb →ₐ[K] Ω | ψ x = algebraMap k Ω E.j} : Set (Fb →ₐ[K] Ω)).Finite :=
    Set.finite_coe_iff.1 hfinNE
  have horbfin : (MulAction.orbit (Ω ≃ₐ[k] Ω) ψ₀).Finite := hNEfin.subset horb_sub
  have hidxψ_le : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀).index ≤
      (CohCarrier.GammaH M ⊥ ⊔ Subgroup.zpowers (-1)).index := by
    rw [MulAction.index_stabilizer]
    calc (MulAction.orbit (Ω ≃ₐ[k] Ω) ψ₀).ncard
        ≤ ({ψ : Fb →ₐ[K] Ω | ψ x = algebraMap k Ω E.j} : Set (Fb →ₐ[K] Ω)).ncard :=
          Set.ncard_le_ncard horb_sub hNEfin
      _ = Nat.card {ψ : Fb →ₐ[K] Ω // ψ x = algebraMap k Ω E.j} := by
          rw [← Nat.card_coe_set_eq]; rfl
      _ ≤ _ := hcardNE.trans hdegU
  have hidxψ_ne : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀).index ≠ 0 := by
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos horbfin).2 ⟨ψ₀, MulAction.mem_orbit_self ψ₀⟩).ne'

  by_cases hM1 : M = 1
  · subst hM1
    refine ⟨0, ψ₀, addOrderOf_zero, hψ₀x, fun σ _ => ?_⟩
    have htop : CohCarrier.GammaH 1 ⊥ ⊔ Subgroup.zpowers (-1) = ⊤ := by
      refine eq_top_iff.2 (le_trans ?_ le_sup_left)
      rw [ModularCurve.GammaH_bot, Gamma1_one_eq_top]
    rw [htop, Subgroup.index_top] at hidxψ_le
    have h1 : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀).index = 1 := by omega
    rw [Subgroup.index_eq_one] at h1
    have hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀ := by rw [h1]; exact Subgroup.mem_top σ
    exact (hstabψ σ).1 hσ

  have hM2 : 2 ≤ M := by
    have := NeZero.ne M
    omega
  haveI : NeZero (M : K) := ⟨hM⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  let T : WeierstrassCurve F := tateLaurent K
  let TL : WeierstrassCurve L := T.baseChange L
  let EL : WeierstrassCurve L := E.baseChange L
  haveI : TL.IsElliptic := show (T.map _).IsElliptic from inferInstance
  haveI : EL.IsElliptic := show (E.map _).IsElliptic from inferInstance
  have hTLj : TL.j = algebraMap F L (jqModC K) := by
    change (T.map (algebraMap F L)).j = _
    rw [WeierstrassCurve.map_j, ModularCurve.j_tateLaurent]
  have hELj : EL.j = algebraMap F L (jqModC K) := by
    change (E.map (algebraMap k L)).j = _
    rw [WeierstrassCurve.map_j, hιL, hιj]
  have hTLtr : Transcendental K TL.j := by
    rw [hTLj]
    exact (transcendental_algebraMap_iff (algebraMap F L).injective).2 hyt
  have hELtr : Transcendental K EL.j := by
    rw [hELj]
    exact (transcendental_algebraMap_iff (algebraMap F L).injective).2 hyt
  have hTc₄ : TL.c₄ ≠ 0 := c₄_ne_zero_of_transcendental_j TL hTLtr
  have hTc₆ : TL.c₆ ≠ 0 := c₆_ne_zero_of_transcendental_j TL hTLtr
  have hEc₄ : EL.c₄ ≠ 0 := c₄_ne_zero_of_transcendental_j EL hELtr
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (E := TL) (E' := EL)
    (hTLj.trans hELj.symm)
  obtain ⟨e, he⟩ := exists_pointEquiv_of_smul_eq C TL EL hC

  obtain ⟨PT, hPTord, hPTlaw⟩ :=
    ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot K M hM2 ζ hζ L
  have hPT0 : M • PT = 0 := (hPTord M).2 (dvd_refl M)
  have hPTM : addOrderOf PT = M := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_iff_nsmul_eq_zero.2 hPT0) ?_
    exact (hPTord _).1 (addOrderOf_nsmul_eq_zero PT)
  have hM1dvd : ¬ M ∣ 1 := fun h => hM1 (Nat.dvd_one.1 h)
  obtain ⟨hns1, hPT1⟩ := hPTlaw 1 hM1dvd
  rw [one_nsmul] at hPT1
  set Xs : F := (toricPoint K 1 ζ).1 with hXs
  set XL : L := algebraMap F L (toricPoint K 1 (ζ ^ 1)).1 with hXL
  set YL : L := algebraMap F L (toricPoint K 1 (ζ ^ 1)).2 with hYL
  have hXLs : XL = algebraMap F L Xs := by rw [hXL, hXs, pow_one]

  set PE : EL.toAffine.Point := e.symm PT with hPE
  have hPEM : addOrderOf PE = M := by rw [hPE, AddEquiv.addOrderOf_eq, hPTM]
  have hePE : e PE = PT := by rw [hPE, AddEquiv.apply_symm_apply]

  obtain ⟨xE, yE, hxyE, hPExy⟩ : ∃ (xE yE : L) (h : EL.toAffine.Nonsingular xE yE),
      PE = .some xE yE h := by
    refine exists_eq_some_of_ne_zero PE fun h0 => ?_
    rw [h0, addOrderOf_zero] at hPEM
    exact hM1 hPEM.symm
  have hXrel : (C.u : L) ^ 2 * xE + C.r = XL := by
    obtain ⟨h', he'⟩ := he xE yE hxyE
    have h1 : e PE = .some XL YL hns1 := by rw [hePE, hPT1]
    rw [hPExy, he'] at h1
    exact (Point.some.inj h1).1

  have hTa₁ : TL.a₁ = 1 := by
    change (T.map (algebraMap F L)).a₁ = 1
    rw [WeierstrassCurve.map_a₁]; change algebraMap F L (tateLaurent K).a₁ = 1
    rw [tateLaurent_a₁, map_one]
  have hTa₂ : TL.a₂ = 0 := by
    change (T.map (algebraMap F L)).a₂ = 0
    rw [WeierstrassCurve.map_a₂]; change algebraMap F L (tateLaurent K).a₂ = 0
    rw [tateLaurent_a₂, map_zero]
  have hTa₃ : TL.a₃ = 0 := by
    change (T.map (algebraMap F L)).a₃ = 0
    rw [WeierstrassCurve.map_a₃]; change algebraMap F L (tateLaurent K).a₃ = 0
    rw [tateLaurent_a₃, map_zero]
  have hTb₂ : TL.b₂ = 1 := by
    simp only [WeierstrassCurve.b₂, hTa₁, hTa₂]; ring
  have hTb₄ : TL.b₄ = 2 * TL.a₄ := by
    simp only [WeierstrassCurve.b₄, hTa₁, hTa₃]; ring
  have hTa₄ : TL.a₄ = algebraMap F L T.a₄ := by
    change (T.map (algebraMap F L)).a₄ = _
    rw [WeierstrassCurve.map_a₄]
  have hTc₄' : TL.c₄ = algebraMap F L T.c₄ := by
    change (T.map (algebraMap F L)).c₄ = _
    rw [WeierstrassCurve.map_c₄]
  have hTc₆' : TL.c₆ = algebraMap F L T.c₆ := by
    change (T.map (algebraMap F L)).c₆ = _
    rw [WeierstrassCurve.map_c₆]

  set uu : L := (C.u : L) with huu
  set vv : L := ((C.u⁻¹ : Lˣ) : L) with hvv
  have hvu : vv * uu = 1 := by
    rw [hvv, huu, Units.val_inv_eq_inv_val]; exact inv_mul_cancel₀ C.u.ne_zero
  have hEb₂ : EL.b₂ = vv ^ 2 * (1 + 12 * C.r) := by
    rw [← hC, variableChange_b₂, hTb₂]
  have hEb₄ : EL.b₄ = vv ^ 4 * (2 * TL.a₄ + C.r + 6 * C.r ^ 2) := by
    rw [← hC, variableChange_b₄, hTb₂, hTb₄]; ring
  have hEc₄' : EL.c₄ = vv ^ 4 * TL.c₄ := by rw [← hC, variableChange_c₄]
  have hEc₆' : EL.c₆ = vv ^ 6 * TL.c₆ := by rw [← hC, variableChange_c₆]
  have hvv0 : vv ≠ 0 := by rw [hvv]; exact (C.u⁻¹).ne_zero

  have hI1 : 12 * xE + EL.b₂ = vv ^ 2 * (1 + 12 * XL) := by
    rw [hEb₂, ← hXrel]
    linear_combination (-(12 * xE * (vv * uu + 1))) * hvu

  have hI2 : 6 * xE ^ 2 + EL.b₂ * xE + EL.b₄ = vv ^ 4 * (XL + 6 * XL ^ 2 + 2 * TL.a₄) := by
    rw [hEb₂, hEb₄, ← hXrel]
    have hvu2 : vv ^ 2 * uu ^ 2 = 1 := by
      calc vv ^ 2 * uu ^ 2 = (vv * uu) ^ 2 := by ring
        _ = 1 := by rw [hvu, one_pow]
    have hvu4 : vv ^ 4 * uu ^ 4 = 1 := by
      calc vv ^ 4 * uu ^ 4 = (vv * uu) ^ 4 := by ring
        _ = 1 := by rw [hvu, one_pow]
    linear_combination (-(6 * xE ^ 2)) * hvu4 + (-(vv ^ 2 * xE) - 12 * vv ^ 2 * C.r * xE) * hvu2

  obtain ⟨hg₁, hg₂⟩ :=
    ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1 K M hM2 ζ hζ
  set g₁ : Fb := ⟨T.c₄ * (1 + 12 * Xs) / T.c₆, hg₁⟩ with hg₁def
  set g₂ : Fb := ⟨(Xs + 6 * Xs ^ 2 + 2 * T.a₄) / T.c₄, hg₂⟩ with hg₂def
  have hθg₁ : θ g₁ = TL.c₄ * (1 + 12 * XL) / TL.c₆ := by
    rw [hθ, hTc₄', hTc₆', hXLs]
    change algebraMap F L (T.c₄ * (1 + 12 * Xs) / T.c₆) = _
    simp only [map_div₀, map_mul, map_add, map_one, map_ofNat]
  have hθg₂ : θ g₂ = (XL + 6 * XL ^ 2 + 2 * TL.a₄) / TL.c₄ := by
    rw [hθ, hTc₄', hTa₄, hXLs]
    change algebraMap F L ((Xs + 6 * Xs ^ 2 + 2 * T.a₄) / T.c₄) = _
    simp only [map_div₀, map_mul, map_add, map_pow, map_ofNat]

  have hv2 : vv ^ 2 = EL.c₆ * TL.c₄ / (EL.c₄ * TL.c₆) := by
    rw [hEc₄', hEc₆', eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hvv0) hTc₄) hTc₆)]
    ring
  have hJ1 : 12 * xE + EL.b₂ = EL.c₆ / EL.c₄ * θ g₁ := by
    rw [hI1, hv2, hθg₁, div_mul_eq_mul_div, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hEc₄ hTc₆) (mul_ne_zero hEc₄ hTc₆)]
    ring
  have hJ2 : 6 * xE ^ 2 + EL.b₂ * xE + EL.b₄ = EL.c₄ * θ g₂ := by
    rw [hI2, hθg₂, hEc₄', ← mul_div_assoc, eq_div_iff hTc₄]
    ring

  set S : IntermediateField K L := θ.fieldRange with hSdef
  have hSθ : ∀ g : Fb, θ g ∈ S := fun g => ⟨g, rfl⟩
  have hSk : ∀ z : k, algebraMap k L z ∈ S := by
    intro z
    let ιKL : k →ₐ[K] L := (IsScalarTower.toAlgHom K F L).comp ι
    have hιKL : ∀ z, ιKL z = algebraMap k L z := fun z => rfl
    have hz : z ∈ (⊤ : IntermediateField K k) := IntermediateField.mem_top
    rw [← hgen] at hz
    have hmap : (IntermediateField.adjoin K ({E.j} : Set k)).map ιKL ≤ S := by
      rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hιKL, hιL, hιj]
      have : θ x = algebraMap F L (jqModC K) := by rw [hθ, hx]
      rw [← this]
      exact hSθ x
    rw [← hιKL]
    exact hmap ⟨z, hz, rfl⟩
  have hSa : ∀ w : k, algebraMap k L w ∈ S := hSk
  have hSb₂ : EL.b₂ ∈ S := by
    have : EL.b₂ = algebraMap k L E.b₂ := by
      change (E.map (algebraMap k L)).b₂ = _; rw [WeierstrassCurve.map_b₂]
    rw [this]; exact hSa _
  have hSb₄ : EL.b₄ ∈ S := by
    have : EL.b₄ = algebraMap k L E.b₄ := by
      change (E.map (algebraMap k L)).b₄ = _; rw [WeierstrassCurve.map_b₄]
    rw [this]; exact hSa _
  have hSc₄ : EL.c₄ ∈ S := by
    have : EL.c₄ = algebraMap k L E.c₄ := by
      change (E.map (algebraMap k L)).c₄ = _; rw [WeierstrassCurve.map_c₄]
    rw [this]; exact hSa _
  have hSc₆ : EL.c₆ ∈ S := by
    have : EL.c₆ = algebraMap k L E.c₆ := by
      change (E.map (algebraMap k L)).c₆ = _; rw [WeierstrassCurve.map_c₆]
    rw [this]; exact hSa _

  have hxES : xE ∈ S := by
    by_cases h6 : (6 : K) = 0
    ·
      have h6L : (6 : L) = 0 := by
        have := congrArg (algebraMap K L) h6
        rwa [map_ofNat, map_zero] at this
      have h24L : (24 : L) = 0 := by
        have : (24 : L) = 4 * 6 := by norm_num
        rw [this, h6L, mul_zero]
      have hc₄b : EL.c₄ = EL.b₂ ^ 2 := by
        have : EL.c₄ = EL.b₂ ^ 2 - 24 * EL.b₄ := rfl
        rw [this, h24L, zero_mul, sub_zero]
      have hb₂0 : EL.b₂ ≠ 0 := by
        intro h0
        apply hEc₄
        rw [hc₄b, h0, zero_pow two_ne_zero]
      have hlin : EL.b₂ * xE = EL.c₄ * θ g₂ - EL.b₄ := by
        have := hJ2
        rw [show (6 : L) * xE ^ 2 = 0 by rw [h6L, zero_mul], zero_add] at this
        linear_combination this
      have hxeq : xE = (EL.c₄ * θ g₂ - EL.b₄) * EL.b₂⁻¹ := by
        rw [← hlin, mul_comm EL.b₂ xE, mul_assoc, mul_inv_cancel₀ hb₂0, mul_one]
      rw [hxeq]
      exact mul_mem (sub_mem (mul_mem hSc₄ (hSθ g₂)) hSb₄) (inv_mem hSb₂)
    ·
      have h2 : (2 : K) ≠ 0 := by
        intro h2
        apply h6
        rw [show (6 : K) = 2 * 3 by norm_num, h2, zero_mul]
      have h12 : (12 : K) ≠ 0 := by
        rw [show (12 : K) = 2 * 6 by norm_num]
        exact mul_ne_zero h2 h6
      have h12L : (12 : L) ≠ 0 := by
        intro h0
        apply h12
        apply (algebraMap K L).injective
        rw [map_ofNat, map_zero, h0]
      have hxeq : xE = (EL.c₆ / EL.c₄ * θ g₁ - EL.b₂) * (12 : L)⁻¹ := by
        rw [← hJ1, add_sub_cancel_right, mul_comm (12 : L) xE, mul_assoc, mul_inv_cancel₀ h12L,
          mul_one]
      rw [hxeq]
      refine mul_mem (sub_mem (mul_mem (div_mem hSc₆ hSc₄) (hSθ g₁)) hSb₂) (inv_mem ?_)
      exact IntermediateField.natCast_mem S 12
  obtain ⟨w, hw⟩ : ∃ w : Fb, θ w = xE := AlgHom.mem_fieldRange.1 hxES

  let ιp : (E.baseChange Ω).toAffine.Point →+ EL.toAffine.Point := Point.map ιΩ
  have hιp : Function.Injective ιp := Point.map_injective ιΩ
  have htorΩ : Nat.card {Q : (E.baseChange Ω).toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := Ω) E M hMΩ
  have htorL : Nat.card {Q : EL.toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := L) E M hML
  have hPE0 : M • PE = 0 := nsmul_of_addOrderOf_eq M hPEM
  obtain ⟨P₀, -, hP₀⟩ := exists_eq_of_nsmul_eq_zero ιp hιp M htorΩ htorL PE hPE0
  have hP₀M : addOrderOf P₀ = M := by
    have := addOrderOf_injective ιp hιp P₀
    rw [hP₀, hPEM] at this
    exact this.symm

  obtain ⟨x₀, y₀, hxy₀, hP₀xy⟩ : ∃ (x₀ y₀ : Ω) (h : (E.baseChange Ω).toAffine.Nonsingular x₀ y₀),
      P₀ = .some x₀ y₀ h := by
    refine exists_eq_some_of_ne_zero P₀ fun h0 => ?_
    rw [h0, addOrderOf_zero] at hP₀M
    exact hM1 hP₀M.symm
  have hx₀ : ιΩ x₀ = xE := by
    have h1 : ιp P₀ = .some xE yE hxyE := by rw [hP₀, hPExy]
    rw [hP₀xy] at h1
    exact (Point.some.inj h1).1
  have hψ₀w : ψ₀ w = x₀ := by
    apply hιΩKinj
    rw [hψ₀, hw, hιΩK, hx₀]

  let s₀ : Cls (E.baseChange Ω).toAffine.Point M := ⟨orbb M P₀, P₀, hP₀M, rfl⟩
  have hstab_s₀ : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ MulAction.stabilizer (Ω ≃ₐ[k] Ω) s₀ ↔
      Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀ := by
    intro σ
    rw [MulAction.mem_stabilizer_iff]
    exact smul_cls_eq_iff M σ s₀ hP₀M rfl

  have htrans : ∀ P P' : (E.baseChange Ω).toAffine.Point, addOrderOf P = M → addOrderOf P' = M →
      ∃ σ : Ω ≃ₐ[k] Ω, P' = σ • P := fun P P' hP hP' =>
    WeierstrassCurve.exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j K M hM k Ω E hE hgen
      P P' hP hP'
  obtain ⟨eM⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hMΩ
  have hcls : Nat.card (Cls (E.baseChange Ω).toAffine.Point M) =
      (CohCarrier.GammaH M ⊥ ⊔ Subgroup.zpowers (-1)).index :=
    AddCommGroup.natCard_torsionOrbit_gammaH_eq_index M ⊥ eM
  have hidxH : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) s₀).index =
      (CohCarrier.GammaH M ⊥ ⊔ Subgroup.zpowers (-1)).index := by
    rw [index_stabilizer_cls M htrans s₀, hcls]

  have hle : MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀ ≤ MulAction.stabilizer (Ω ≃ₐ[k] Ω) s₀ := by
    intro σ hσ
    rw [hstab_s₀]
    have hσψ : ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ := (hstabψ σ).1 hσ
    have hσx₀ : σ x₀ = x₀ := by
      have := congrArg (fun φ : Fb →ₐ[K] Ω => φ w) hσψ
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
      rw [hψ₀w] at this
      exact this
    rw [hP₀xy, Point.map_some]
    exact (Point.X_eq_iff (h₁ := _) (h₂ := hxy₀)).1 hσx₀

  have hge : MulAction.stabilizer (Ω ≃ₐ[k] Ω) s₀ ≤ MulAction.stabilizer (Ω ≃ₐ[k] Ω) ψ₀ :=
    le_of_index_le hle (by rw [hidxH]; exact hidxψ_le) hidxψ_ne

  refine ⟨P₀, ψ₀, hP₀M, hψ₀x, fun σ hσ => ?_⟩
  exact (hstabψ σ).1 (hge ((hstab_s₀ σ).2 hσ))

end Main

end P2MKcKron
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg.P2MKcKron"

universe u v in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₀ : (E.baseChange Ω).toAffine.Point)
      (ψ₀ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω),
      addOrderOf P₀ = M ∧ ψ₀ x = algebraMap k Ω E.j ∧
      ∀ σ : Ω ≃ₐ[k] Ω,
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨
          WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) →
        ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ :=
  P2MKcKron.main K M hM x hx k Ω E hE hgen

end
end S_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg
end P2MW
export P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gamma1_comp_eq_of_map_eq_or_eq_neg (solution)
