-- Prove2me | solution 1 for ModularCurve.moduliPlace_orbitClauses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0e535e78-162f-58e3-90e1-4008fcac68c4

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPlace_orbitClauses
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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped IntermediateField

noncomputable section

namespace P2MKcModuliOrbit

universe u

section Cast

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem heq_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) :=
  (castPt_eq_iff_heq e P _).mp rfl

theorem castPt_injective {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    Function.Injective (castPt e) :=
  (castPt e).injective

theorem map_castPt_rfl {W : WeierstrassCurve L} (H : AddSubgroup W.toAffine.Point) :
    H.map (castPt (rfl : W = W)).toAddMonoidHom = H := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩; exact hQ
  · intro hP; exact ⟨P, hP, rfl⟩

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

def vcInvHom (γ : VariableChange L) (W : WeierstrassCurve L) :
    W.toAffine.Point →+ (γ • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine)

@[scoped simp] theorem vcInvHom_apply (γ : VariableChange L) (W : WeierstrassCurve L)
    (P : W.toAffine.Point) : vcInvHom γ W P = Point.vcInvFun γ W.toAffine P := rfl

theorem vcInvFun_injective (γ : VariableChange L) (W : WeierstrassCurve L) :
    Function.Injective (Point.vcInvFun γ W.toAffine) :=
  (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective

theorem vcInvFun_nsmul (γ : VariableChange L) (W : WeierstrassCurve L) (n : ℕ)
    (P : W.toAffine.Point) :
    Point.vcInvFun γ W.toAffine (n • P) = n • Point.vcInvFun γ W.toAffine P :=
  map_nsmul (vcInvHom γ W) n P

theorem vcInvFun_some (γ : VariableChange L) (W : WeierstrassCurve L) {x y : L}
    (h : W.toAffine.Nonsingular x y) :
    ∃ h', Point.vcInvFun γ W.toAffine (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) h' :=
  ⟨_, rfl⟩

theorem heq_some_vcInvFun {V V' : WeierstrassCurve L} (γ : VariableChange L)
    (hV : V'.toAffine = (γ • V).toAffine) {x y : L} (h : V.toAffine.Nonsingular x y) {x' y' : L}
    {h' : V'.toAffine.Nonsingular x' y'} (hx : x' = vcXInv γ x) (hy : y' = vcYInv γ x y) :
    HEq (Point.some x' y' h' : V'.toAffine.Point) (Point.vcInvFun γ V.toAffine (.some x y h)) := by
  obtain ⟨h'', hh⟩ := vcInvFun_some γ V h
  rw [hh]
  exact ModularCurve.Point.heq_some hV hx hy

end Cast

section CycSub

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ)

abbrev CycSub (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

variable {N}

private theorem _root_.P2MKcModuliOrbit.exists_generator (hN : N ≠ 0) (H : CycSub A N) :
    ∃ g : A, addOrderOf g = N ∧ AddSubgroup.zmultiples g = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "P2MKcModuliOrbit" "exists_generator"

def cycOf (g : A) (hg : addOrderOf g = N) : CycSub A N :=
  ⟨AddSubgroup.zmultiples g, ⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, hg]⟩

@[scoped simp] theorem cycOf_val (g : A) (hg : addOrderOf g = N) :
    (cycOf g hg).1 = AddSubgroup.zmultiples g := rfl

theorem nsmul_eq_zero_of_mem (H : CycSub A N) {x : A} (hx : x ∈ H.1) : N • x = 0 := by
  have h : Nat.card H.1 • (⟨x, hx⟩ : H.1) = 0 := card_nsmul_eq_zero'
  rw [H.2.2] at h
  exact congrArg Subtype.val h

def mapCyc (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) : CycSub B N := by
  refine ⟨H.1.map φ, ?_, ?_⟩
  · obtain ⟨hc, -⟩ := H.2
    haveI := hc
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
    refine ⟨⟨⟨φ g.1, AddSubgroup.mem_map_of_mem φ g.2⟩, fun y => ?_⟩⟩
    obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp y.2
    obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : n • g.1 = x := congrArg Subtype.val hn
    simp only [AddSubgroup.coe_zsmul, ← hxy, ← hn', map_zsmul]
  · have h := Nat.card_image_of_injOn hφ
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
    have hc : Nat.card (H.1.map φ) = Nat.card H.1 := by
      rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe H.1, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq, AddSubgroup.coe_map]
      exact h
    exact hc.trans H.2.2

@[scoped simp] theorem mapCyc_val (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) :
    (mapCyc φ H hφ).1 = H.1.map φ := rfl

def tors (A : Type*) [AddCommGroup A] (N : ℕ) : Set A := {x | N • x = 0}

theorem subset_tors (H : CycSub A N) : (H.1 : Set A) ⊆ tors A N :=
  fun _ hx => nsmul_eq_zero_of_mem H hx

theorem injOn_of_injOn_tors {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) (H : CycSub A N) :
    Set.InjOn φ H.1 :=
  hφ.mono (subset_tors H)

theorem mapCyc_injective {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) {H H' : CycSub A N}
    (h : mapCyc φ H (injOn_of_injOn_tors hφ H) = mapCyc φ H' (injOn_of_injOn_tors hφ H')) :
    H = H' := by
  have h1 : (φ '' (H.1 : Set A)) = φ '' (H'.1 : Set A) := by
    have := congrArg (fun X : CycSub B N => ((X.1 : AddSubgroup B) : Set B)) h
    simpa only [mapCyc_val, AddSubgroup.coe_map] using this
  have h2 : (H.1 : Set A) = H'.1 := (hφ.image_eq_image_iff (subset_tors H) (subset_tors H')).mp h1
  exact Subtype.ext (SetLike.coe_injective h2)

theorem mapCyc_surjective (hN : N ≠ 0) {φ : A →+ B} (hφ : Set.InjOn φ (tors A N))
    (hsurj : ∀ y ∈ tors B N, ∃ x ∈ tors A N, φ x = y) (H₀ : CycSub B N) :
    ∃ H : CycSub A N, mapCyc φ H (injOn_of_injOn_tors hφ H) = H₀ := by
  obtain ⟨g₀, hg₀, hgen⟩ := exists_generator hN H₀
  have hg₀t : g₀ ∈ tors B N := by
    show N • g₀ = 0
    rw [← hg₀]; exact addOrderOf_nsmul_eq_zero g₀
  obtain ⟨g, hgt, hgφ⟩ := hsurj g₀ hg₀t
  have hordg : addOrderOf g = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hgt) ?_
    rw [← hg₀, ← hgφ]
    exact addOrderOf_map_dvd φ g
  refine ⟨cycOf g hordg, Subtype.ext ?_⟩
  show (AddSubgroup.zmultiples g).map φ = H₀.1
  rw [AddMonoidHom.map_zmultiples, hgφ, hgen]

theorem eq_of_le_of_card_eq {H H' : AddSubgroup B} (hle : H ≤ H') (hH : Nat.card H = N)
    (hH' : Nat.card H' = N) (hN : N ≠ 0) : H = H' := by
  haveI : Finite H' := Nat.finite_of_card_ne_zero (by rw [hH']; exact hN)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hH, hH'])

theorem map_neg_eq (H : AddSubgroup B) : H.map (-(AddMonoidHom.id B)) = H := by
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.neg_apply, AddMonoidHom.id_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact H.neg_mem hy
  · intro hx; exact ⟨-x, H.neg_mem hx, neg_neg x⟩

theorem addOrderOf_map_eq (φ : A →+ B) {P : A} (hP : addOrderOf P = N)
    (hinj : ∀ Q : A, N • Q = 0 → φ Q = 0 → Q = 0) : addOrderOf (φ P) = N := by
  refine Nat.dvd_antisymm ?_ ?_
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← hP, addOrderOf_nsmul_eq_zero, map_zero]
  · set m := addOrderOf (φ P) with hm
    have h1 : φ (m • P) = 0 := by rw [map_nsmul]; exact addOrderOf_nsmul_eq_zero (φ P)
    have h2 : N • (m • P) = 0 := by
      rw [smul_smul, mul_comm, ← smul_smul, ← hP, addOrderOf_nsmul_eq_zero, smul_zero]
    have h3 : m • P = 0 := hinj _ h2 h1
    rw [← hP]
    exact addOrderOf_dvd_of_nsmul_eq_zero h3

end CycSub

section Assemble

variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} {N : ℕ}
variable {Pt : Type*} [AddCommGroup Pt]
variable {G : Type*}
variable {X : Type*}
variable {Pl : Type*}

def Rel (E₀ : WeierstrassCurve L) (N : ℕ) (H H' : CycSub E₀.toAffine.Point N) : Prop :=
  ∃ γ : VariableChange L, γ • E₀ = E₀ ∧
    ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'

theorem Rel_iff (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, ∀ T ∈ H.1, autPt γ hγ T ∈ H'.1 := by
  unfold Rel
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := h T hT
    rwa [(autPt_eq_iff_heq γ hγ T T').mpr hh]
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun T hT => ⟨autPt γ hγ T, h T hT, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩

theorem Rel_iff_map_eq (hN : N ≠ 0) (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, H.1.map (autPt γ hγ) = H'.1 := by
  rw [Rel_iff]
  refine exists_congr fun γ => exists_congr fun hγ => ?_
  constructor
  · intro h
    have hle : H.1.map (autPt γ hγ) ≤ H'.1 := by
      rintro _ ⟨T, hT, rfl⟩; exact h T hT
    have hcard : Nat.card (H.1.map (autPt γ hγ)) = N :=
      (mapCyc (autPt γ hγ) H ((autPt_injective γ hγ).injOn)).2.2
    exact eq_of_le_of_card_eq hle hcard H'.2.2 hN
  · intro h T hT
    rw [← h]; exact AddSubgroup.mem_map_of_mem _ hT

theorem assemble (hN : N ≠ 0)
    (θ : Pt →+ E₀.toAffine.Point) (hθ : Set.InjOn θ (tors Pt N))
    (hθs : ∀ y ∈ tors E₀.toAffine.Point N, ∃ x ∈ tors Pt N, θ x = y)
    (D : G → Prop) (act : G → (Pt →+ Pt)) (hact : ∀ σ, Function.Injective (act σ))
    (ρ : G → VariableChange L) (hρ : ∀ σ, D σ → ρ σ • E₀ = E₀)
    (hequiv : ∀ σ (hσ : D σ) (P : Pt), θ (act σ P) = autPt (ρ σ) (hρ σ hσ) (θ P))
    (hsurj : ∀ (γ : VariableChange L) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))))
    (Φ : CycSub Pt N ≃ X) (actX : G → X → X)
    (hnat : ∀ σ (H : CycSub Pt N), Φ (mapCyc (act σ) H (hact σ).injOn) = actX σ (Φ H))
    (π : X → Pl) (S : Pl → Prop) (hπS : ∀ x, S (π x)) (hπsurj : ∀ P, S P → ∃ x, π x = P)
    (hπfib : ∀ x x', π x = π x' ↔ ∃ σ, D σ ∧ x' = actX σ x)
    (e : Pl → ℤ) (hπe : ∀ x, e (π x) = Nat.card {x' // π x' = π x})
    (f : CycSub E₀.toAffine.Point N → Pl)
    (hf : ∀ H : CycSub Pt N, f (mapCyc θ H (injOn_of_injOn_tors hθ H)) = π (Φ H)) :
    (∀ H, S (f H)) ∧ (∀ P, S P → ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ Rel E₀ N H H') ∧
      ∀ H, e (f H) = Nat.card {H' // f H' = f H} := by
  classical

  let Ξf : CycSub Pt N → CycSub E₀.toAffine.Point N := fun H => mapCyc θ H (injOn_of_injOn_tors hθ H)
  have hΞ : Function.Bijective Ξf :=
    ⟨fun H H' h => mapCyc_injective hθ h, fun H₀ => mapCyc_surjective hN hθ hθs H₀⟩
  let Ξ : CycSub Pt N ≃ CycSub E₀.toAffine.Point N := Equiv.ofBijective Ξf hΞ
  have Ξ_val : ∀ H, (Ξ H).1 = H.1.map θ := fun H => rfl

  let ε : CycSub E₀.toAffine.Point N ≃ X := Ξ.symm.trans Φ
  have hfε : ∀ H₀, f H₀ = π (ε H₀) := by
    intro H₀
    have h := hf (Ξ.symm H₀)
    have h' : mapCyc θ (Ξ.symm H₀) (injOn_of_injOn_tors hθ _) = Ξ (Ξ.symm H₀) := rfl
    rw [h', Equiv.apply_symm_apply] at h
    exact h
  refine ⟨fun H₀ => (hfε H₀) ▸ hπS _, ?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨x, hx⟩ := hπsurj P hP
    exact ⟨ε.symm x, by rw [hfε, Equiv.apply_symm_apply, hx]⟩
  ·
    intro H₀ H₀'
    rw [hfε, hfε, hπfib, Rel_iff_map_eq hN]

    have key : ∀ σ (hσ : D σ) (H : CycSub Pt N),
        (Ξ (mapCyc (act σ) H (hact σ).injOn)).1 = (Ξ H).1.map (autPt (ρ σ) (hρ σ hσ)) := by
      intro σ hσ H
      rw [Ξ_val, Ξ_val, mapCyc_val, AddSubgroup.map_map, AddSubgroup.map_map]
      congr 1
      ext P
      exact hequiv σ hσ P
    constructor
    · rintro ⟨σ, hσ, hx⟩
      have h1 : Φ (Ξ.symm H₀') = Φ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) := by
        rw [hnat]; exact hx
      have h2 : Ξ.symm H₀' = mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn := Φ.injective h1
      refine ⟨ρ σ, hρ σ hσ, ?_⟩
      have h3 := key σ hσ (Ξ.symm H₀)
      rw [← h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3
      exact h3.symm
    · rintro ⟨γ, hγ, hmap⟩
      obtain ⟨σ, hσ, hsgn⟩ := hsurj γ hγ
      refine ⟨σ, hσ, ?_⟩
      have h1 : (Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn)).1 = H₀'.1 := by
        rw [Ξ_val, mapCyc_val, AddSubgroup.map_map]
        have hH₀ : (Ξ.symm H₀).1.map θ = H₀.1 := by
          rw [← Ξ_val, Equiv.apply_symm_apply]
        rcases hsgn with h | h
        · have hc : θ.comp (act σ) = (autPt γ hγ).comp θ := by ext P; exact h P
          rw [hc, ← AddSubgroup.map_map, hH₀, hmap]
        · have hc : θ.comp (act σ) = (-(AddMonoidHom.id _)).comp ((autPt γ hγ).comp θ) := by
            ext P; simp [h P]
          rw [hc, ← AddSubgroup.map_map, ← AddSubgroup.map_map, hH₀, hmap, map_neg_eq]
      have h2 : Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) = H₀' := Subtype.ext h1
      show Φ (Ξ.symm H₀') = actX σ (Φ (Ξ.symm H₀))
      rw [← hnat, ← h2, Equiv.symm_apply_apply]
  ·
    intro H₀
    rw [hfε, hπe]
    congr 1
    refine Nat.card_congr ((Equiv.subtypeEquiv ε fun H₀' => ?_).symm)
    show f H₀' = π (ε H₀) ↔ π (ε H₀') = π (ε H₀)
    rw [hfε]

end Assemble

section Supplies

theorem isIntegral_of_apply_eq {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F]
    [Algebra K M] (x : F) (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨q, hqm, hq0⟩ := hy
  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩
  have hlifts : q.map (algebraMap K⟮t⟯ M) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem card_tors (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {N : ℕ} [NeZero N]
    (hN : (N : K) ≠ 0) : Nat.card (tors E₀.toAffine.Point N) = N ^ 2 := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) E₀ hN
  have hb : (E₀⁄K) = E₀.toAffine := by
    show (E₀.baseChange K).toAffine = E₀.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hmem : ∀ P : E₀.toAffine.Point,
      P ∈ Submodule.torsionBy ℤ E₀.toAffine.Point N ↔ P ∈ tors _ N := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    show ((N : ℤ) • P = 0) ↔ N • P = 0
    rw [natCast_zsmul]
  have hset : (Submodule.torsionBy ℤ E₀.toAffine.Point N : Set E₀.toAffine.Point) = tors _ N :=
    Set.ext hmem
  have h1 : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← SetLike.coe_sort_coe, hset] at h1
  exact h1

omit [DecidableEq K] [IsAlgClosed K] in

theorem eq_of_ord_sub_algebraMap_pos {F : Type*} [Field F] [Algebra K F] (v : Place K F) (f : F)
    {a b : K} (ha : 0 < v.ord (f - algebraMap K F a)) (hb : 0 < v.ord (f - algebraMap K F b)) :
    a = b := by
  by_contra hab

  have hmax : ∀ g : F, 0 < v.ord g → ∃ hg : g ∈ v.toValuationSubring,
      (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    intro g hg
    have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    have hmem : g ∈ v.toValuationSubring := (ComapPlace.mem_iff_ord_nonneg v hg0).mpr hg.le
    refine ⟨hmem, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord g = 0 at this
    omega
  obtain ⟨hma, hma'⟩ := hmax _ ha
  obtain ⟨hmb, hmb'⟩ := hmax _ hb
  have hsub := Ideal.sub_mem _ hmb' hma'

  have hconst : (⟨f - algebraMap K F b, hmb⟩ : v.toValuationSubring) - ⟨f - algebraMap K F a, hma⟩ =
      ⟨algebraMap K F (a - b), v.algebraMap_mem' _⟩ := by
    apply Subtype.ext
    change (f - algebraMap K F b) - (f - algebraMap K F a) = algebraMap K F (a - b)
    rw [map_sub]
    ring
  rw [hconst] at hsub
  apply (IsLocalRing.mem_maximalIdeal _).mp hsub
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨⟨⟨algebraMap K F (a - b), v.algebraMap_mem' _⟩,
    ⟨algebraMap K F (a - b)⁻¹, v.algebraMap_mem' _⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · change algebraMap K F (a - b) * algebraMap K F (a - b)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hab', map_one]
  · change algebraMap K F (a - b)⁻¹ * algebraMap K F (a - b) = 1
    rw [← map_mul, inv_mul_cancel₀ hab', map_one]

end Supplies

section PlaceJ0

variable (K : Type*) [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]

theorem adjoin_toSubring_eq_closure (t : M) :
    (Algebra.adjoin K ({t} : Set M)).toSubring =
      Subring.closure (Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) ∪ {t}) := by
  have hr : Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) =
      Set.range (algebraMap K M) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, ValuationSubring.mem_top a⟩, rfl⟩
  rw [hr]
  ext x
  rw [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff]

theorem exists_place_ord_pos (t : M) (htr : Transcendental K t) [FiniteDimensional K⟮t⟯ M]
    [Algebra.IsSeparable K⟮t⟯ M] (j₀ : K) :
    ∃ W₀ : Place K M, 0 < W₀.ord (t - algebraMap K M j₀) := by
  let A : ValuationSubring K := ⊤
  let B : Subring M := (Algebra.adjoin K ({t} : Set M)).toSubring
  have hconst : ∀ a : A, algebraMap K M a ∈ B := fun a =>
    (Algebra.adjoin K ({t} : Set M)).algebraMap_mem a
  have htB : t ∈ B := Algebra.self_mem_adjoin_singleton K t
  have hint : ∀ b : B, IsIntegral
      (Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})) (b : M) := by
    intro b
    have hb : (b : M) ∈ Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t}) := by
      rw [← adjoin_toSubring_eq_closure]; exact b.2
    exact isIntegral_algebraMap (A := M)
      (x := (⟨(b : M), hb⟩ : Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})))

  let g : B := ⟨t, htB⟩ - ⟨algebraMap K M j₀, hconst ⟨j₀, ValuationSubring.mem_top j₀⟩⟩
  have hg : ¬ IsUnit g := by
    intro hu
    let e := Polynomial.algEquivOfTranscendental K t htr
    have hge : e (Polynomial.X - Polynomial.C j₀) = g := by
      apply Subtype.ext
      simp [e, g, Polynomial.algEquivOfTranscendental_apply]
    have : IsUnit (Polynomial.X - Polynomial.C j₀ : Polynomial K) := by
      rw [← hge] at hu
      exact (MulEquiv.isUnit_map e).mp hu
    exact Polynomial.not_isUnit_X_sub_C j₀ this
  obtain ⟨𝔮, h𝔮max, hg𝔮⟩ := Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_ne_top hg)
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A →
      (⟨algebraMap K M a, hconst a⟩ : B) ∈ 𝔮 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      apply (IsLocalRing.mem_maximalIdeal _).mp ha
      have hne' : (a : K) ≠ 0 := fun h => hne (Subtype.ext h)
      exact ⟨⟨a, ⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩,
        Subtype.ext (mul_inv_cancel₀ hne'), Subtype.ext (inv_mul_cancel₀ hne')⟩, rfl⟩
    have : (⟨algebraMap K M a, hconst a⟩ : B) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [this]; exact 𝔮.zero_mem
  have hja : (⟨t, htB⟩ : B) - ⟨algebraMap K M ((⟨j₀, ValuationSubring.mem_top j₀⟩ : A) : K),
      hconst _⟩ ∈ 𝔮 := hg𝔮 (Ideal.mem_span_singleton_self g)
  obtain ⟨w, hw, -⟩ := AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring A htr hconst htB
    hint 𝔮 h𝔮A ⟨j₀, ValuationSubring.mem_top j₀⟩ hja
  exact ⟨w, hw⟩

end PlaceJ0

section PinBridge

variable {M Ω' : Type*} [Field M] [Field Ω'] [DecidableEq M] [DecidableEq Ω']

theorem cyclicQuotientJ_castPt {V₁ V₂ : WeierstrassCurve Ω'} (h : V₁ = V₂)
    (H : AddSubgroup V₁.toAffine.Point) (d : ℕ) :
    V₂.cyclicQuotientJ (H.map (castPt h).toAddMonoidHom) d = V₁.cyclicQuotientJ H d := by
  subst h
  rw [map_castPt_rfl]

theorem mem_zmultiples_vcInvFun_iff (C : VariableChange Ω') (W : WeierstrassCurve Ω')
    (X : W.toAffine.Point) (Q : (C • W).toAffine.Point) :
    Q ∈ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine X) ↔
      Point.vcFun C W.toAffine Q ∈ AddSubgroup.zmultiples X := by
  have hl := Point.vcFun_leftInverse (C := C) (W := W.toAffine)
  rw [show AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine X) =
      (AddSubgroup.zmultiples X).map (vcInvHom C W) from
    (AddMonoidHom.map_zmultiples (vcInvHom C W) X).symm]
  conv_lhs => rw [← hl Q]
  exact AddSubgroup.mem_map_iff_mem (vcInvFun_injective C W)

theorem pin_bridge (σ : M →+* Ω') (V : WeierstrassCurve M) (κ₀ : VariableChange M)
    {WAM : WeierstrassCurve M} (hκ₀ : κ₀ • V = WAM) (P : V.toAffine.Point) (n d : ℕ)
    (hd : (d : Ω') ≠ 0) :
    (WAM.map σ).cyclicQuotientJ
        (AddSubgroup.zmultiples
          (WeierstrassCurve.mapPoint σ (n • castPt hκ₀ (Point.vcInvFun κ₀ V.toAffine P)))) d =
      (V.map σ).cyclicQuotientJ
        (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint σ (n • P))) d := by
  subst hκ₀
  have h3 : (κ₀.map σ) • (V.map σ) = (κ₀ • V).map σ := V.map_variableChange κ₀ σ

  have hpt : ∀ h0 : κ₀ • V = κ₀ • V, castPt h3.symm (WeierstrassCurve.mapPoint σ
      (n • castPt h0 (Point.vcInvFun κ₀ V.toAffine P))) =
      Point.vcInvFun (κ₀.map σ) (V.map σ).toAffine (WeierstrassCurve.mapPoint σ (n • P)) := by
    intro h0
    rw [castPt_eq_iff_heq]
    have h1 : n • castPt h0 (Point.vcInvFun κ₀ V.toAffine P) =
        Point.vcInvFun κ₀ V.toAffine (n • P) := by
      rw [vcInvFun_nsmul]; rfl
    rw [h1]
    exact ModularCurve.mapPoint_vcInvFun_heq σ κ₀ V (n • P)
  rw [← cyclicQuotientJ_castPt h3.symm, AddMonoidHom.map_zmultiples, AddEquiv.coe_toAddMonoidHom,
    hpt]
  exact WeierstrassCurve.cyclicQuotientJ_variableChange_eq (κ₀.map σ) (V.map σ)
    (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint σ (n • P))) _
    (mem_zmultiples_vcInvFun_iff _ _ _) d hd

theorem baseChange_bridge {k : Type*} [Field k] [Algebra k M] [Algebra k Ω'] [Algebra M Ω']
    [IsScalarTower k M Ω'] (E : WeierstrassCurve k) (Q : (E.baseChange M).toAffine.Point) (d : ℕ) :
    ((E.baseChange M).map (algebraMap M Ω')).cyclicQuotientJ
        (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap M Ω') Q)) d =
      (E.baseChange Ω').cyclicQuotientJ
        ((AddSubgroup.zmultiples Q).map
          (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k M Ω'))) d := by
  have h4 : (E.baseChange M).map (algebraMap M Ω') = E.baseChange Ω' := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq]
  rw [← cyclicQuotientJ_castPt h4, AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples,
    AddEquiv.coe_toAddMonoidHom]
  congr 2
  rw [castPt_eq_iff_heq]
  cases Q with
  | zero => exact ModularCurve.Point.heq_zero (congrArg WeierstrassCurve.toAffine h4)
  | some x y h =>
    rw [WeierstrassCurve.mapPoint_some, WeierstrassCurve.Affine.Point.map_some]
    exact ModularCurve.Point.heq_some (congrArg WeierstrassCurve.toAffine h4) rfl rfl

end PinBridge

section Datum

variable {K : Type u} [Field K] [DecidableEq K] {N : ℕ} [NeZero N]
variable {M : Type u} [Field M] [DecidableEq M] [Algebra K M]
variable {V : WeierstrassCurve M} (W₀ : Place K M)
variable {WA : WeierstrassCurve W₀.toValuationSubring} {κ₀ : VariableChange M}
  (e : ResidueField W₀.toValuationSubring ≃+* K) {γ₀ : VariableChange K}
  (hΔ : (WA.map (residue W₀.toValuationSubring)).Δ ≠ 0)
  {E₀ : WeierstrassCurve K} [hE₀ : E₀.IsElliptic]
  (θ : V.toAffine.Point →+ E₀.toAffine.Point)
  (hκ₀ : κ₀ • V = WA.map W₀.toValuationSubring.subtype)

def ξ : V.toAffine.Point →+ (WA.map W₀.toValuationSubring.subtype).toAffine.Point :=
  (castPt hκ₀).toAddMonoidHom.comp (vcInvHom κ₀ V)

theorem ξ_apply (P : V.toAffine.Point) :
    ξ W₀ hκ₀ P = castPt hκ₀ (Point.vcInvFun κ₀ V.toAffine P) := rfl

theorem heq_ξ (P : V.toAffine.Point) : HEq (Point.vcInvFun κ₀ V.toAffine P) (ξ W₀ hκ₀ P) :=
  heq_castPt hκ₀ _

theorem ξ_injective : Function.Injective (ξ W₀ hκ₀) :=
  (castPt hκ₀).injective.comp (vcInvFun_injective κ₀ V)

variable (he : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c)
  (hγ₀ : γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = E₀)
  (hθ0 : letI := Classical.decEq (ResidueField W₀.toValuationSubring)
    ∀ (P : V.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point),
      HEq (Point.vcInvFun κ₀ V.toAffine P) P₁ → reduceHom hΔ P₁ = 0 → θ P = 0)
  (hθsome : letI := Classical.decEq (ResidueField W₀.toValuationSubring)
    ∀ (P : V.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point)
      (x y : ResidueField W₀.toValuationSubring)
      (h : (WA.map (residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
      HEq (Point.vcInvFun κ₀ V.toAffine P) P₁ → reduceHom hΔ P₁ = Point.some x y h →
      ∃ h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (e x)) (vcYInv γ₀ (e x) (e y)),
        θ P = Point.some _ _ h')
  (hθinj : ∀ P : V.toAffine.Point, N • P = 0 → θ P = 0 → P = 0)
  (hN : (N : K) ≠ 0)
  (P : V.toAffine.Point) (hP : addOrderOf P = N)
  (ψ : modularFunctionFieldFullC K N →ₐ[K] M)
  (hpin : ∀ (Ω' : Type u) [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] [Algebra M Ω']
      (d : ℕ) [NeZero d] (hd : d ∣ N),
      algebraMap M Ω' (ψ (jqNFull K N d hd)) =
        (V.map (algebraMap M Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • P))) d)

include hP hθinj in

theorem addOrderOf_θ : addOrderOf (θ P) = N :=
  addOrderOf_map_eq θ hP hθinj

include hP hθ0 hθinj in

theorem addOrderOf_reduceHom_ξ :
    letI := Classical.decEq (ResidueField W₀.toValuationSubring)
    addOrderOf (reduceHom hΔ (ξ W₀ hκ₀ P)) = N := by
  letI := Classical.decEq (ResidueField W₀.toValuationSubring)
  refine addOrderOf_map_eq ((reduceHom hΔ).comp (ξ W₀ hκ₀)) hP fun Q hQ h0 => ?_
  exact hθinj Q hQ (hθ0 Q (ξ W₀ hκ₀ Q) (heq_ξ W₀ hκ₀ Q) h0)

include hγ₀ hθ0 hθsome hθinj in

theorem map_mk_reduce_eq :
    letI := Classical.decEq (ResidueField W₀.toValuationSubring)
    ModuliPoint.map e.toRingHom
      (Quot.mk _ (⟨WA.map (residue W₀.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩, reduceHom hΔ (ξ W₀ hκ₀ P),
          addOrderOf_reduceHom_ξ W₀ hΔ θ hκ₀ hθ0 hθinj P hP⟩ :
            Gamma0Pair N (ResidueField W₀.toValuationSubring))) =
      Quot.mk _ (⟨E₀, hE₀, θ P, addOrderOf_θ θ hθinj P hP⟩ : Gamma0Pair N K) := by
  letI := Classical.decEq (ResidueField W₀.toValuationSubring)
  rw [ModuliPoint.map_mk]
  refine Quot.sound ⟨γ₀, hγ₀, 1, Nat.coprime_one_left N, ?_⟩
  show HEq (θ P) ((1 : ℕ) • Point.vcInvFun γ₀
    ((WA.map (residue W₀.toValuationSubring)).map e.toRingHom).toAffine
      (WeierstrassCurve.mapPoint e.toRingHom (reduceHom hΔ (ξ W₀ hκ₀ P))))
  rw [one_smul]
  have hV : E₀.toAffine = (γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).toAffine :=
    (congrArg WeierstrassCurve.toAffine hγ₀).symm
  rcases hr : reduceHom hΔ (ξ W₀ hκ₀ P) with _ | ⟨x, y, hxy⟩
  · rw [hθ0 P _ (heq_ξ W₀ hκ₀ P) hr]
    exact ModularCurve.Point.heq_zero hV
  · obtain ⟨h', hθ⟩ := hθsome P _ x y hxy (heq_ξ W₀ hκ₀ P) hr
    rw [hθ, WeierstrassCurve.mapPoint_some]
    exact heq_some_vcInvFun γ₀ hV _ rfl rfl

include hκ₀ he hγ₀ hθ0 hθsome hθinj hN hpin in

theorem isModuliPlaceOf_of_reduction (hψ : ψ.toRingHom.IsIntegral) :
    IsModuliPlaceOf K N (Quot.mk _ (⟨E₀, hE₀, θ P, addOrderOf_θ θ hθinj P hP⟩ : Gamma0Pair N K))
      (W₀.restrictAlong ψ hψ) := by
  let D : ModuliTestDatum K N
      (Quot.mk _ (⟨E₀, hE₀, θ P, addOrderOf_θ θ hθinj P hP⟩ : Gamma0Pair N K)) M :=
    { W := W₀
      curve := WA
      map_Δ_ne_zero := hΔ
      gen := ξ W₀ hκ₀ P
      addOrderOf_gen := by rw [addOrderOf_injective _ (ξ_injective W₀ hκ₀) P, hP]
      res := e.toRingHom
      res_algebraMap := he
      reduction := ⟨addOrderOf_reduceHom_ξ W₀ hΔ θ hκ₀ hθ0 hθinj P hP,
        map_mk_reduce_eq W₀ e hΔ θ hκ₀ hγ₀ hθ0 hθsome hθinj P hP⟩
      emb := ψ
      emb_jqNFull := by
        intro Ω' _ _ _ _ d _ hd
        have hdK : (d : K) ≠ 0 := by
          intro h0
          obtain ⟨c, hc⟩ := hd
          apply hN
          rw [hc, Nat.cast_mul, h0, zero_mul]
        have hdΩ : (d : Ω') ≠ 0 := by
          rw [← map_natCast (algebraMap M Ω'), ← map_natCast (algebraMap K M),
            map_ne_zero, map_ne_zero]
          exact hdK
        rw [hpin Ω' d hd]
        exact (pin_bridge (algebraMap M Ω') V κ₀ hκ₀ P (N / d) d hdΩ).symm }
  exact ⟨M, ‹_›, ‹_›, ‹_›, D, rfl⟩

end Datum

section OneCurve

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

def jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

theorem oneCurve (hN : (N : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint N K) (v v' : Place K (modularFunctionFieldFullC K N)),
      IsModuliPlaceOf K N x v → IsModuliPlaceOf K N x v' → v = v')
    (E₀ : WeierstrassCurve K) [hE₀ : E₀.IsElliptic] :
    (∀ C : CycSub E₀.toAffine.Point N,
        0 < (moduliPlace K N E₀ C.1).ord (jF K N - algebraMap K _ E₀.j)) ∧
    (∀ Q : Place K (modularFunctionFieldFullC K N), 0 < Q.ord (jF K N - algebraMap K _ E₀.j) →
        ∃ C : CycSub E₀.toAffine.Point N, moduliPlace K N E₀ C.1 = Q) ∧
    (∀ C C' : CycSub E₀.toAffine.Point N,
        moduliPlace K N E₀ C.1 = moduliPlace K N E₀ C'.1 ↔ Rel E₀ N C C') ∧
    (∀ C : CycSub E₀.toAffine.Point N,
        (moduliPlace K N E₀ C.1).ord (jF K N - algebraMap K _ E₀.j) =
          Nat.card {C' : CycSub E₀.toAffine.Point N //
            moduliPlace K N E₀ C'.1 = moduliPlace K N E₀ C.1}) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let F := modularFunctionFieldFullC K N
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)

  obtain ⟨M, _iF, _iD, _iA, t, ht, hfin, hgal, hfull, hC1⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom K p N hN
  haveI := hfin
  haveI := hgal

  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  let E : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ tk
  have hEj : E.j = tk := WeierstrassCurve.ofJ_j tk
  have hjt : algebraMap K⟮t⟯ M E.j = t := by rw [hEj]; rfl
  have hEtr : Transcendental K E.j := by
    rw [hEj]
    intro halg
    exact ht (by simpa using halg.algebraMap (A := M))

  obtain ⟨Φ, hnatA, hpins⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
      K N hN K⟮t⟯ M E hEtr hfull

  obtain ⟨W₀, hW₀⟩ := exists_place_ord_pos K t ht E₀.j
  obtain ⟨WA, κ₀, e, γ₀, hΔ, θ, ρ, hκ₀, -, he, hγ₀, hθ0, hθsome, hθinj, hρE, -, hequivC,
    hsurjC, -⟩ := @hC1 E₀.j E₀ hE₀ rfl W₀ (Classical.decEq _) hW₀
  have hθinjN : ∀ P : (E.baseChange M).toAffine.Point, N • P = 0 → θ P = 0 → P = 0 :=
    fun P h1 h2 => hθinj N P hpN h1 h2

  let X : Type _ := {ψ : F →ₐ[K] M // ψ (jF K N) = t}
  let embX : {ψ : F →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap K⟮t⟯ M E.j} ≃ X :=
    Equiv.subtypeEquivRight (fun ψ => by rw [hjt]; rfl)
  let ΦX : CycSub (E.baseChange M).toAffine.Point N ≃ X := Φ.trans embX
  have ΦX_val : ∀ H, (ΦX H).1 = (Φ H).1 := fun H => rfl

  have hint : ∀ ψ : F →ₐ[K] M, ψ (jF K N) = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq (jF K N) t ψ hψ

  have hcard₀ := card_tors E₀ hN
  have hθ : Set.InjOn θ (tors (E.baseChange M).toAffine.Point N) := by
    intro P hP Q hQ h
    have hPQ : N • (P - Q) = 0 := by
      rw [nsmul_sub, show N • P = 0 from hP, show N • Q = 0 from hQ, sub_zero]
    have := hθinjN (P - Q) hPQ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hθs : ∀ y ∈ tors E₀.toAffine.Point N,
      ∃ x ∈ tors (E.baseChange M).toAffine.Point N, θ x = y := by
    let θr : tors (E.baseChange M).toAffine.Point N → tors E₀.toAffine.Point N :=
      fun P => ⟨θ P.1, show N • θ P.1 = 0 by rw [← map_nsmul, show N • P.1 = 0 from P.2, map_zero]⟩
    have hinj : Function.Injective θr := fun P Q h =>
      Subtype.ext (hθ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite (tors E₀.toAffine.Point N) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 hN0)
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hcard₀]
      exact le_of_eq hfull.symm)
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : E₀.toAffine.Point, addOrderOf g₀ = N := by
    obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := K) (K := K) E₀ hN
    have hb : (E₀⁄K) = E₀.toAffine := by
      show (E₀.baseChange K).toAffine = E₀.toAffine
      rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hb] at eT
    refine ⟨(eT (1, 0)).1, ?_⟩
    have h1 : addOrderOf ((eT (1, 0)).1) = addOrderOf (eT (1, 0)) :=
      addOrderOf_injective (Submodule.torsionBy ℤ E₀.toAffine.Point N).subtype.toAddMonoidHom
        Subtype.val_injective (eT (1, 0))
    rw [h1, AddEquiv.addOrderOf_eq eT, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
      Nat.lcm_one_right]
  obtain ⟨H₁, -⟩ := mapCyc_surjective hN0 hθ hθs (cycOf g₀ hg₀)
  let ι : F →ₐ[K] M := (ΦX H₁).1
  have hι : ι (jF K N) = t := (ΦX H₁).2

  obtain ⟨-, hBi, hBii, hBiii, hBiv⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K (jF K N) t E₀.j ι hι
      hfin hgal hint W₀ hW₀

  let D : (M ≃ₐ[K⟮t⟯] M) → Prop := fun σ =>
    SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀
  let act : (M ≃ₐ[K⟮t⟯] M) →
      ((E.baseChange M).toAffine.Point →+ (E.baseChange M).toAffine.Point) :=
    fun σ => WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)
  have hact : ∀ σ, Function.Injective (act σ) := fun σ =>
    WeierstrassCurve.Affine.Point.map_injective (W' := E) (σ : M →ₐ[K⟮t⟯] M)
  have hσt : ∀ σ : M ≃ₐ[K⟮t⟯] M, σ t = t := fun σ => σ.commutes tk
  let actX : (M ≃ₐ[K⟮t⟯] M) → X → X := fun σ ψ =>
    ⟨((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ.1, by
      show σ (ψ.1 (jF K N)) = t
      rw [ψ.2, hσt]⟩
  have hnat : ∀ σ (H : CycSub (E.baseChange M).toAffine.Point N),
      ΦX (mapCyc (act σ) H (hact σ).injOn) = actX σ (ΦX H) := by
    intro σ H
    apply Subtype.ext
    rw [ΦX_val]
    exact hnatA σ H (mapCyc (act σ) H (hact σ).injOn) rfl

  have hequiv : ∀ σ (hσ : D σ) (P : (E.baseChange M).toAffine.Point),
      θ (act σ P) = autPt (ρ σ) (hρE σ hσ) (θ P) :=
    fun σ hσ P => ((autPt_eq_iff_heq _ _ _ _).mpr (hequivC σ hσ P)).symm
  have hsurj : ∀ (γ : VariableChange K) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))) := by
    intro γ hγ
    obtain ⟨σ, hσ, h⟩ := hsurjC γ hγ
    refine ⟨σ, hσ, ?_⟩
    rcases h with h | h
    · exact Or.inl fun P => ((autPt_eq_iff_heq _ _ _ _).mpr (h P)).symm
    · refine Or.inr fun P => ?_
      have := (autPt_eq_iff_heq γ hγ (θ P) _).mpr (h P)
      rw [this, neg_neg]

  let π : X → Place K F := fun ψ => W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)
  let S : Place K F → Prop := fun Q => 0 < Q.ord (jF K N - algebraMap K F E₀.j)
  have hπS : ∀ ψ, S (π ψ) := fun ψ => hBi ψ.1 ψ.2
  have hπsurj : ∀ Q, S Q → ∃ ψ, π ψ = Q := by
    intro Q hQ
    obtain ⟨ψ, hψ, h⟩ := hBii Q hQ
    exact ⟨⟨ψ, hψ⟩, h⟩
  have hπfib : ∀ ψ ψ' : X, π ψ = π ψ' ↔ ∃ σ, D σ ∧ ψ' = actX σ ψ := by
    intro ψ ψ'
    rw [show (π ψ = π ψ') = (W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2) =
      W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2)) from rfl, hBiii ψ.1 ψ'.1 ψ.2 ψ'.2]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    rw [Subtype.ext_iff]
  let eram : Place K F → ℤ := fun Q => Q.ord (jF K N - algebraMap K F E₀.j)
  have hπe : ∀ ψ : X, eram (π ψ) = Nat.card {ψ' // π ψ' = π ψ} := fun ψ => hBiv ψ.1 ψ.2

  have hf : ∀ H : CycSub (E.baseChange M).toAffine.Point N,
      moduliPlace K N E₀ (mapCyc θ H (injOn_of_injOn_tors hθ H)).1 = π (ΦX H) := by
    intro H
    obtain ⟨P, hP, hPH⟩ := exists_generator hN0 H
    have hmapθ : (mapCyc θ H (injOn_of_injOn_tors hθ H)).1 = AddSubgroup.zmultiples (θ P) := by
      rw [mapCyc_val, ← hPH, AddMonoidHom.map_zmultiples]

    have hpin : ∀ (Ω' : Type u) [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] [Algebra M Ω']
        (d : ℕ) [NeZero d] (hd : d ∣ N),
        algebraMap M Ω' ((ΦX H).1 (jqNFull K N d hd)) =
          ((E.baseChange M).map (algebraMap M Ω')).cyclicQuotientJ
            (AddSubgroup.zmultiples
              (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • P))) d := by
      intro Ω' _ _ _ _ d _ hd

      have hordd : addOrderOf ((N / d) • P) = d := by
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hN0)
        have hq : 0 < N / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd) hd0
        rw [addOrderOf_nsmul' _ hq.ne', hP, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
          Nat.div_div_self hd hN0]
      have hle : (cycOf ((N / d) • P) hordd).1 ≤ H.1 := by
        rw [cycOf_val, AddSubgroup.zmultiples_le, ← hPH]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples P) _
      have h := hpins Ω' H d hd (cycOf ((N / d) • P) hordd) hle
      rw [ΦX_val, baseChange_bridge]
      exact h
    have hIs := isModuliPlaceOf_of_reduction W₀ e hΔ θ hκ₀ he hγ₀ hθ0 hθsome hθinjN hN P hP
      (ΦX H).1 hpin (hint _ (ΦX H).2)
    rw [hmapθ, moduliPlace_zmultiples K N E₀ (θ P) (addOrderOf_θ θ hθinjN P hP),
      moduliPlaceOfPoint_eq_of_forall_eq K N (huniq _) hIs]

  obtain ⟨h1, h2, h3, h4⟩ := assemble hN0 θ hθ hθs D act hact ρ hρE hequiv hsurj ΦX actX
    hnat π S hπS hπsurj hπfib eram hπe (fun C => moduliPlace K N E₀ C.1) hf
  exact ⟨h1, h2, h3, h4⟩

end OneCurve

section Across

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem heq_vcInvFun_mul (δ γ : VariableChange K) (E : WeierstrassCurve K) (T : E.toAffine.Point) :
    HEq (Point.vcInvFun (δ * γ) E.toAffine T)
      (Point.vcInvFun δ (γ • E).toAffine (Point.vcInvFun γ E.toAffine T)) := by
  have hE : ((δ * γ) • E).toAffine = (δ • γ • E).toAffine := by rw [mul_smul]
  cases T with
  | zero => exact ModularCurve.Point.heq_zero hE
  | some x y h =>
    obtain ⟨h₁, e₁⟩ := vcInvFun_some (δ * γ) E h
    obtain ⟨h₂, e₂⟩ := vcInvFun_some γ E h
    rw [e₁, e₂]
    obtain ⟨h₃, e₃⟩ := vcInvFun_some δ (γ • E) h₂
    rw [e₃]
    refine ModularCurve.Point.heq_some hE ?_ ?_
    · have hu : (δ.u : K) ≠ 0 := δ.u.ne_zero
      have hu' : (γ.u : K) ≠ 0 := γ.u.ne_zero
      simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
      field_simp
      ring
    · have hu : (δ.u : K) ≠ 0 := δ.u.ne_zero
      have hu' : (γ.u : K) ≠ 0 := γ.u.ne_zero
      simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
      field_simp
      ring

theorem moduliPlace_eq_of_variableChange (E E' : WeierstrassCurve K) [hE : E.IsElliptic]
    [hE' : E'.IsElliptic] (C : CycSub E.toAffine.Point N) (C' : CycSub E'.toAffine.Point N)
    (γ : VariableChange K) (hγ : γ • E = E')
    (h : ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') :
    moduliPlace K N E C.1 = moduliPlace K N E' C'.1 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  subst hγ
  obtain ⟨g, hg, hgC⟩ := exists_generator hN0 C

  let g' : (γ • E).toAffine.Point := Point.vcInvFun γ E.toAffine g
  have hg'C : g' ∈ C'.1 := by
    obtain ⟨T', hT', hh⟩ := h g (hgC ▸ AddSubgroup.mem_zmultiples g)
    rwa [← eq_of_heq hh] at hT'
  have hg' : addOrderOf g' = N := by
    rw [← hg]; exact addOrderOf_injective (vcInvHom γ E) (vcInvFun_injective γ E) g
  have hgC' : AddSubgroup.zmultiples g' = C'.1 := by
    refine eq_of_le_of_card_eq (AddSubgroup.zmultiples_le.mpr hg'C) ?_ C'.2.2 hN0
    rw [Nat.card_zmultiples, hg']
  rw [← hgC, ← hgC', moduliPlace_zmultiples K N E g hg, moduliPlace_zmultiples K N (γ • E) g' hg']
  congr 1
  refine Quot.sound ⟨γ, rfl, 1, Nat.coprime_one_left N, ?_⟩
  show HEq g' ((1 : ℕ) • Point.vcInvFun γ E.toAffine g)
  rw [one_smul]

def transportCyc {E : WeierstrassCurve K} (γ : VariableChange K) (C : CycSub E.toAffine.Point N) :
    CycSub (γ • E).toAffine.Point N :=
  mapCyc (vcInvHom γ E) C (vcInvFun_injective γ E).injOn

theorem mem_transportCyc {E : WeierstrassCurve K} (γ : VariableChange K)
    (C : CycSub E.toAffine.Point N) {T : E.toAffine.Point} (hT : T ∈ C.1) :
    Point.vcInvFun γ E.toAffine T ∈ (transportCyc K N γ C).1 :=
  AddSubgroup.mem_map_of_mem (vcInvHom γ E) hT

theorem exists_of_mem_transportCyc {E : WeierstrassCurve K} (γ : VariableChange K)
    (C : CycSub E.toAffine.Point N) {T' : (γ • E).toAffine.Point}
    (hT' : T' ∈ (transportCyc K N γ C).1) : ∃ T ∈ C.1, Point.vcInvFun γ E.toAffine T = T' :=
  AddSubgroup.mem_map.mp hT'

end Across

end P2MKcModuliOrbit
p2m_reactivate "P2MW.S_ModularCurve_moduliPlace_orbitClauses.P2MKcModuliOrbit"

end
p2m_reactivate "P2MW.S_ModularCurve_moduliPlace_orbitClauses.P2MKcModuliOrbit"

open P2MKcModuliOrbit in
universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint N K) (v v' : Place K (modularFunctionFieldFullC K N)),
      IsModuliPlaceOf K N x v → IsModuliPlaceOf K N x v' → v = v') :
    (∀ (E : WeierstrassCurve K) [E.IsElliptic]
        (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N}),
        0 < (moduliPlace K N E C.1).ord
          ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
            algebraMap K (modularFunctionFieldFullC K N) E.j)) ∧
    (∀ (E : WeierstrassCurve K) [E.IsElliptic] (P : Place K (modularFunctionFieldFullC K N)),
        0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
          algebraMap K (modularFunctionFieldFullC K N) E.j) →
        ∃ C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N},
          moduliPlace K N E C.1 = P) ∧
    (∀ (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
        (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N})
        (C' : {C : AddSubgroup E'.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N}),
        moduliPlace K N E C.1 = moduliPlace K N E' C'.1 ↔ ∃ γ : VariableChange K, γ • E = E' ∧
          ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') ∧
    (∀ (E : WeierstrassCurve K) [E.IsElliptic]
        (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N}),
        (moduliPlace K N E C.1).ord
            ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
              algebraMap K (modularFunctionFieldFullC K N) E.j) =
          (Nat.card {C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N} //
            moduliPlace K N E C'.1 = moduliPlace K N E C.1} : ℤ)) := by
  refine ⟨fun E _ C => (oneCurve K N hN huniq E).1 C,
    fun E _ P hP => (oneCurve K N hN huniq E).2.1 P hP, ?_,
    fun E _ C => (oneCurve K N hN huniq E).2.2.2 C⟩
  intro E E' _ _ C C'
  constructor
  · intro hCC'

    have h1 := (oneCurve K N hN huniq E).1 C
    have h2 := (oneCurve K N hN huniq E').1 C'
    rw [← hCC'] at h2
    have hj : E.j = E'.j := eq_of_ord_sub_algebraMap_pos _ _ h1 h2
    obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq E E' hj
    subst hγ

    have h3 : moduliPlace K N E C.1 = moduliPlace K N (γ • E) (transportCyc K N γ C).1 :=
      moduliPlace_eq_of_variableChange K N E (γ • E) C _ γ rfl
        fun T hT => ⟨_, mem_transportCyc K N γ C hT, HEq.rfl⟩
    rw [h3] at hCC'
    obtain ⟨δ, hδ, hδC⟩ := ((oneCurve K N hN huniq (γ • E)).2.2.1 _ _).mp hCC'
    refine ⟨δ * γ, by rw [mul_smul, hδ], fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := hδC _ (mem_transportCyc K N γ C hT)
    exact ⟨T', hT', (heq_vcInvFun_mul K δ γ E T).trans hh⟩
  · rintro ⟨γ, hγ, h⟩
    exact moduliPlace_eq_of_variableChange K N E E' C C' γ hγ h

end S_ModularCurve_moduliPlace_orbitClauses
end P2MW
export P2MW.S_ModularCurve_moduliPlace_orbitClauses (solution)
