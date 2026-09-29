-- Prove2me | solution 1 for ModularCurve.moduliPoint_eq_of_isModuliPlaceOf_of_isModuliPlaceOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/86c5a440-e94b-57e3-a457-2464435d2d1b

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPoint_eq_of_isModuliPlaceOf_of_isModuliPlaceOf
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false

namespace PlaceInjSol

open ModularCurve AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type} [Field K] [DecidableEq K]

noncomputable def vcInvHom (C : VariableChange K) (W : WeierstrassCurve.Affine K) :
    W.Point →+ (C • W).toAffine.Point where
  toFun := Point.vcInvFun C W
  map_zero' := Point.vcInvFun_zero
  map_add' := Point.vcInvFun_add C W

theorem vcInvHom_apply (C : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    vcInvHom C W P = Point.vcInvFun C W P := rfl

theorem vcInvFun_injective (C : VariableChange K) (W : WeierstrassCurve.Affine K) :
    Function.Injective (Point.vcInvFun C W) :=
  (Point.vcFun_rightInverse (C := C) (W := W)).injective

theorem addOrderOf_vcInvFun (C : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    addOrderOf (Point.vcInvFun C W P) = addOrderOf P := by
  rw [← vcInvHom_apply]
  exact addOrderOf_injective (vcInvHom C W) (vcInvFun_injective C W) P

theorem vcInvFun_nsmul (C : VariableChange K) (W : WeierstrassCurve.Affine K) (n : ℕ) (P : W.Point) :
    Point.vcInvFun C W (n • P) = n • Point.vcInvFun C W P := by
  rw [← vcInvHom_apply, map_nsmul]; rfl

theorem vcInvFun_zsmul (C : VariableChange K) (W : WeierstrassCurve.Affine K) (n : ℤ) (P : W.Point) :
    Point.vcInvFun C W (n • P) = n • Point.vcInvFun C W P := by
  rw [← vcInvHom_apply, map_zsmul]; rfl

theorem zmultiples_eq_of_le_of_addOrderOf_eq {A : Type*} [AddGroup A] {a b : A} {N : ℕ} (hN : N ≠ 0)
    (ha : addOrderOf a = N) (hb : addOrderOf b = N)
    (hle : AddSubgroup.zmultiples a ≤ AddSubgroup.zmultiples b) :
    AddSubgroup.zmultiples a = AddSubgroup.zmultiples b := by
  have hcb : Nat.card (AddSubgroup.zmultiples b) = N := by rw [Nat.card_zmultiples, hb]
  have hca : Nat.card (AddSubgroup.zmultiples a) = N := by rw [Nat.card_zmultiples, ha]
  haveI : Finite (AddSubgroup.zmultiples b) := Nat.finite_of_card_ne_zero (hcb ▸ hN)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hca, hcb])

theorem mk_eq_mk_vcInvFun {N : ℕ} (E : WeierstrassCurve K) [hE : E.IsElliptic] (g : E.toAffine.Point)
    (hg : addOrderOf g = N) (γ : VariableChange K) [hE' : (γ • E).IsElliptic]
    (hg' : addOrderOf (Point.vcInvFun γ E.toAffine g) = N) :
    (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K) : ModuliPoint N K) =
      Quot.mk _ (⟨γ • E, hE', Point.vcInvFun γ E.toAffine g, hg'⟩ : Gamma0Pair N K) := by
  refine Quot.sound ⟨γ, rfl, 1, Nat.coprime_one_left N, ?_⟩
  show HEq (Point.vcInvFun γ E.toAffine g) ((1 : ℕ) • Point.vcInvFun γ E.toAffine g)
  rw [one_smul]

end PlaceInjSol

open ModularCurve AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine PlaceInjSol in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (N : ℕ) [NeZero N] (hN : ((N : ℕ) : κ) ≠ 0)
    (x x' : ModularCurve.ModuliPoint N κ) (v : AlgebraicCurve.Place κ ↥(ModularCurve.modularFunctionFieldFullC κ N))
    (hv : ModularCurve.IsModuliPlaceOf κ N x v) (hv' : ModularCurve.IsModuliPlaceOf κ N x' v) : x = x' := by
  classical

  have huniq : ∀ (y : ModuliPoint N κ) (w w' : Place κ (modularFunctionFieldFullC κ N)),
      IsModuliPlaceOf κ N y w → IsModuliPlaceOf κ N y w' → w = w' :=
    fun y w w' h h' => ModularCurve.eq_of_isModuliPlaceOf κ N hN y w w' h h'
  have h1 : moduliPlaceOfPoint κ N x = v := moduliPlaceOfPoint_eq_of_forall_eq κ N (huniq x) hv
  have h1' : moduliPlaceOfPoint κ N x' = v := moduliPlaceOfPoint_eq_of_forall_eq κ N (huniq x') hv'

  induction x using Quot.inductionOn with
  | h P =>
  induction x' using Quot.inductionOn with
  | h P' =>
  obtain ⟨E, hE, g, hg⟩ := P
  obtain ⟨E', hE', g', hg'⟩ := P'
  have hpl : moduliPlace κ N E (AddSubgroup.zmultiples g) = moduliPlace κ N E' (AddSubgroup.zmultiples g') := by
    rw [moduliPlace_zmultiples κ N E g hg, moduliPlace_zmultiples κ N E' g' hg', h1, h1']

  obtain ⟨-, -, h3, -⟩ := ModularCurve.moduliPlace_orbitClauses κ N hN huniq
  have hN0 : N ≠ 0 := NeZero.ne N
  have hcyc : ∀ (F : WeierstrassCurve κ) (a : F.toAffine.Point), addOrderOf a = N →
      IsAddCyclic (AddSubgroup.zmultiples a) ∧ Nat.card (AddSubgroup.zmultiples a) = N := by
    intro F a ha
    exact ⟨AddSubgroup.isAddCyclic_zmultiples a, by rw [Nat.card_zmultiples, ha]⟩
  obtain ⟨γ, hγE, hγC⟩ := (h3 E E' ⟨AddSubgroup.zmultiples g, hcyc E g hg⟩
    ⟨AddSubgroup.zmultiples g', hcyc E' g' hg'⟩).mp hpl
  subst hγE

  obtain ⟨T', hT'mem, hT'⟩ := hγC g (AddSubgroup.mem_zmultiples g)
  have hT'eq : Point.vcInvFun γ E.toAffine g = T' := eq_of_heq hT'
  have hord : addOrderOf (Point.vcInvFun γ E.toAffine g) = N := by
    rw [addOrderOf_vcInvFun, hg]
  have hle : AddSubgroup.zmultiples (Point.vcInvFun γ E.toAffine g) ≤ AddSubgroup.zmultiples g' := by
    rw [AddSubgroup.zmultiples_le, hT'eq]
    exact hT'mem
  have hzeq : AddSubgroup.zmultiples (Point.vcInvFun γ E.toAffine g) = AddSubgroup.zmultiples g' :=
    zmultiples_eq_of_le_of_addOrderOf_eq hN0 hord hg' hle

  calc (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N κ) : ModuliPoint N κ)
      = Quot.mk _ (⟨γ • E, hE', Point.vcInvFun γ E.toAffine g, hord⟩ : Gamma0Pair N κ) :=
        mk_eq_mk_vcInvFun E g hg γ hord
    _ = Quot.mk _ (⟨γ • E, hE', g', hg'⟩ : Gamma0Pair N κ) :=
        ModuliPoint.mk_eq_mk_of_zmultiples_eq hord hg' hzeq

end S_ModularCurve_moduliPoint_eq_of_isModuliPlaceOf_of_isModuliPlaceOf
end P2MW
export P2MW.S_ModularCurve_moduliPoint_eq_of_isModuliPlaceOf_of_isModuliPlaceOf (solution)
