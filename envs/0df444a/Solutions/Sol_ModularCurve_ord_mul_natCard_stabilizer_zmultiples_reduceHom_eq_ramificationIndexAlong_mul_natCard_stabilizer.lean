-- Prove2me | solution 1 for ModularCurve.ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5475caac-a9ce-50ae-9f7b-339954e30c07

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
import Theorems.Thm_ModularCurve_ord_mul_natCard_stabilizer_eq_ramificationIndexAlong_mul_of_equivariant_torsion_reduction
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_and_reduceHom_vcFun_eq
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "WeierstrassCurve~map_veluQuotientOfSums~map_veluGy~map_veluGx WeierstrassCurve.Affine WeierstrassCurve.Affine.Point~some_congr IsLocalRing ValuationSubring AlgebraicCurve ModularCurve~map_vcYInv~map_vcXInv"

open scoped IntermediateField Pointwise

noncomputable section

namespace P2MKcIntrinsicRamif

section Cast

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) : V₁.toAffine.Point ≃+ V₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) (P : V₁.toAffine.Point)
    (Q : V₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

theorem heq_castPt {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) (P : V₁.toAffine.Point) :
    HEq P (castPt e P) := by
  subst e; rfl

theorem castPt_zero {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) : castPt e 0 = 0 := by
  subst e; rfl

theorem castPt_some {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) {x y : L}
    (h : V₁.toAffine.Nonsingular x y) :
    ∃ h' : V₂.toAffine.Nonsingular x y, castPt e (.some x y h) = .some x y h' := by
  subst e; exact ⟨h, rfl⟩

theorem castPt_castPt {V₁ V₂ V₃ : WeierstrassCurve L} (e : V₁ = V₂) (e' : V₂ = V₃)
    (P : V₁.toAffine.Point) : castPt e' (castPt e P) = castPt (e.trans e') P := by
  subst e e'; rfl

theorem some_congr {V : WeierstrassCurve L} {x₁ x₂ y₁ y₂ : L} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂) :
    (Point.some x₁ y₁ h₁ : V.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem fullKernelQuotient_castPt {V₁ V₂ : WeierstrassCurve L} (e : V₁ = V₂) (Q : V₁.toAffine.Point)
    (N : ℕ) : V₂.fullKernelQuotient (castPt e Q) N = V₁.fullKernelQuotient Q N := by
  subst e; rfl

end Cast

section MapPt

variable {L L' : Type*} [Field L] [Field L'] [DecidableEq L] [DecidableEq L']

def mapPt (f : L →+* L') (V : WeierstrassCurve L) : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI : Algebra L L' := f.toAlgebra
  WeierstrassCurve.Affine.Point.map (W' := V.toAffine) (Algebra.ofId L L')

theorem mapPt_zero (f : L →+* L') (V : WeierstrassCurve L) : mapPt f V 0 = 0 := _root_.map_zero _

theorem mapPt_zero' (f : L →+* L') (V : WeierstrassCurve L) : mapPt f V .zero = 0 := _root_.map_zero _

theorem mapPt_some (f : L →+* L') (V : WeierstrassCurve L) {x y : L} (h : V.toAffine.Nonsingular x y) :
    ∃ h', mapPt f V (.some x y h) = .some (f x) (f y) h' :=
  ⟨_, rfl⟩

theorem mapPt_injective (f : L →+* L') (V : WeierstrassCurve L) : Function.Injective (mapPt f V) :=
  letI : Algebra L L' := f.toAlgebra
  WeierstrassCurve.Affine.Point.map_injective (W' := V.toAffine) (Algebra.ofId L L')

omit [DecidableEq L] [DecidableEq L'] in
theorem map_vcXInv (f : L →+* L') (C : VariableChange L) (x : L) :
    f (vcXInv C x) = vcXInv (C.map f) (f x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

omit [DecidableEq L] [DecidableEq L'] in
theorem map_vcYInv (f : L →+* L') (C : VariableChange L) (x y : L) :
    f (vcYInv C x y) = vcYInv (C.map f) (f x) (f y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

omit [DecidableEq L] in
theorem vcXInv_mul (C C' : VariableChange L) (x : L) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

omit [DecidableEq L] in
theorem vcYInv_mul (C C' : VariableChange L) (x y : L) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcInvFun_some (C : VariableChange L) (V : WeierstrassCurve L) {x y : L}
    (h : V.toAffine.Nonsingular x y) :
    ∃ h', Point.vcInvFun C V.toAffine (.some x y h) = .some (vcXInv C x) (vcYInv C x y) h' :=
  ⟨_, rfl⟩

def autPt {V : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • V = V) :
    V.toAffine.Point →+ V.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ V.toAffine) (Point.vcInvFun_add γ V.toAffine))

theorem autPt_apply {V : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • V = V)
    (P : V.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ V.toAffine P) := rfl

theorem autPt_eq_iff_heq {V : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • V = V)
    (P Q : V.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ V.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem autPt_some {V : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • V = V) {x y : L}
    (h : V.toAffine.Nonsingular x y) :
    ∃ h', autPt γ hγ (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) h' := by
  rw [autPt_apply]
  exact castPt_some hγ _

theorem autPt_mul {V : WeierstrassCurve L} (γ γ' : VariableChange L) (hγ : γ • V = V)
    (hγ' : γ' • V = V) (h : (γ * γ') • V = V) (P : V.toAffine.Point) :
    autPt (γ * γ') h P = autPt γ hγ (autPt γ' hγ' P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · show autPt (γ * γ') h 0 = autPt γ hγ (autPt γ' hγ' 0)
    rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
  · obtain ⟨h₁, e₁⟩ := autPt_some (V := V) (γ * γ') h hxy
    obtain ⟨h₂, e₂⟩ := autPt_some (V := V) γ' hγ' hxy
    rw [e₁, e₂]
    obtain ⟨h₃, e₃⟩ := autPt_some (V := V) γ hγ h₂
    rw [e₃]
    exact some_congr (vcXInv_mul γ γ' x) (vcYInv_mul γ γ' x y) _ _

theorem mapPt_autPt {V : WeierstrassCurve L} (f : L →+* L') (γ : VariableChange L) (hγ : γ • V = V)
    (hγ' : (γ.map f) • V.map f = V.map f) (P : V.toAffine.Point) :
    mapPt f V (autPt γ hγ P) = autPt (γ.map f) hγ' (mapPt f V P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · show mapPt f V (autPt γ hγ 0) = autPt (γ.map f) hγ' (mapPt f V 0)
    rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
  · obtain ⟨h₁, e₁⟩ := autPt_some (V := V) γ hγ hxy
    rw [e₁]
    obtain ⟨h₂, e₂⟩ := mapPt_some f V h₁
    obtain ⟨h₃, e₃⟩ := mapPt_some f V hxy
    rw [e₂, e₃]
    obtain ⟨h₄, e₄⟩ := autPt_some (V := V.map f) (γ.map f) hγ' h₃
    rw [e₄]
    exact some_congr (map_vcXInv f γ x) (map_vcYInv f γ x y) _ _

end MapPt

section StabTransport

variable {L L' : Type*} [Field L] [Field L'] [DecidableEq L] [DecidableEq L']

abbrev StabSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) : Type _ :=
  {γ : VariableChange L // γ • V = V ∧
    ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ V.toAffine T) T'}

theorem pres_iff {V : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • V = V)
    (H : AddSubgroup V.toAffine.Point) :
    (∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ V.toAffine T) T') ↔ ∀ T ∈ H, autPt γ hγ T ∈ H := by
  refine forall₂_congr fun T _ => ⟨?_, fun h => ⟨_, h, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩
  rintro ⟨T', hT', h⟩
  rwa [(autPt_eq_iff_heq γ hγ T T').mpr h]

theorem natCard_stabSet_map_autPt (V : WeierstrassCurve L) (ν : VariableChange L) (hν : ν • V = V)
    (H : AddSubgroup V.toAffine.Point) :
    Nat.card (StabSet V (H.map (autPt ν hν))) = Nat.card (StabSet V H) := by

  have hmul : ∀ {a b : VariableChange L}, a • V = V → b • V = V → (a * b) • V = V :=
    fun ha hb => by rw [mul_smul, hb, ha]
  have hinv : ∀ {a : VariableChange L}, a • V = V → a⁻¹ • V = V :=
    fun {a} ha => by conv_lhs => rw [← ha]; rw [inv_smul_smul]
  have h1 : (1 : VariableChange L) • V = V := one_smul _ _

  have hcancel : ∀ (a : VariableChange L) (ha : a • V = V) (T : V.toAffine.Point),
      autPt a⁻¹ (hinv ha) (autPt a ha T) = T := by
    intro a ha T
    rw [← autPt_mul a⁻¹ a (hinv ha) ha (by rw [inv_mul_cancel]; exact h1)]
    have : ∀ (h : (a⁻¹ * a) • V = V), autPt (a⁻¹ * a) h T = T := by
      rw [inv_mul_cancel]; intro h
      rcases T with _ | ⟨x, y, hxy⟩
      · exact _root_.map_zero _
      · obtain ⟨h', e⟩ := autPt_some (V := V) 1 h hxy
        rw [e]; exact some_congr (by simp [vcXInv, VariableChange.one_def])
          (by simp [vcYInv, VariableChange.one_def]) _ _
    exact this _

  refine Nat.card_congr ?_
  refine
    { toFun := fun γ => ⟨ν⁻¹ * γ.1 * ν, hmul (hmul (hinv hν) γ.2.1) hν, ?_⟩
      invFun := fun γ => ⟨ν * γ.1 * ν⁻¹, hmul (hmul hν γ.2.1) (hinv hν), ?_⟩
      left_inv := fun γ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun γ => Subtype.ext (by simp [mul_assoc]) }
  ·
    rw [pres_iff _ (hmul (hmul (hinv hν) γ.2.1) hν)]
    intro T hT
    have hγ := (pres_iff γ.1 γ.2.1 _).mp γ.2.2
    rw [autPt_mul (ν⁻¹ * γ.1) ν (hmul (hinv hν) γ.2.1) hν, autPt_mul ν⁻¹ γ.1 (hinv hν) γ.2.1]
    have h2 : autPt γ.1 γ.2.1 (autPt ν hν T) ∈ H.map (autPt ν hν) :=
      hγ _ (AddSubgroup.mem_map_of_mem _ hT)
    obtain ⟨T', hT', hTT'⟩ := AddSubgroup.mem_map.mp h2
    rw [← hTT', hcancel ν hν]
    exact hT'
  ·
    rw [pres_iff _ (hmul (hmul hν γ.2.1) (hinv hν))]
    rintro _ ⟨T, hT, rfl⟩
    have hγ := (pres_iff γ.1 γ.2.1 _).mp γ.2.2
    rw [autPt_mul (ν * γ.1) ν⁻¹ (hmul hν γ.2.1) (hinv hν), autPt_mul ν γ.1 hν γ.2.1, hcancel ν hν]
    exact AddSubgroup.mem_map_of_mem _ (hγ T hT)

theorem natCard_stabSet_map_ringEquiv (f : L ≃+* L') (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) :
    Nat.card (StabSet (V.map f.toRingHom) (H.map (mapPt f.toRingHom V))) = Nat.card (StabSet V H) := by
  have hfix : ∀ γ : VariableChange L, γ • V = V ↔ (γ.map f.toRingHom) • V.map f.toRingHom = V.map f.toRingHom := by
    intro γ
    rw [map_variableChange]
    constructor
    · intro h; rw [h]
    · intro h; exact WeierstrassCurve.map_injective f.injective h
  have hfix' : ∀ γ : VariableChange L', γ • V.map f.toRingHom = V.map f.toRingHom ↔
      (γ.map f.symm.toRingHom) • V = V := by
    intro γ
    rw [hfix, VariableChange.map_map]
    have : f.toRingHom.comp f.symm.toRingHom = RingHom.id L' := by
      ext x; exact f.apply_symm_apply x
    rw [this, VariableChange.map_id]
  have hpres : ∀ (γ : VariableChange L) (hγ : γ • V = V),
      (∀ T ∈ H, autPt γ hγ T ∈ H) ↔
        ∀ T ∈ H.map (mapPt f.toRingHom V), autPt (γ.map f.toRingHom) ((hfix γ).mp hγ) T ∈
          H.map (mapPt f.toRingHom V) := by
    intro γ hγ
    constructor
    · rintro h _ ⟨T, hT, rfl⟩
      rw [← mapPt_autPt f.toRingHom γ hγ]
      exact AddSubgroup.mem_map_of_mem _ (h T hT)
    · intro h T hT
      have h2 := h _ (AddSubgroup.mem_map_of_mem _ hT)
      rw [← mapPt_autPt f.toRingHom γ hγ] at h2
      obtain ⟨T', hT', hTT'⟩ := AddSubgroup.mem_map.mp h2
      rw [← mapPt_injective f.toRingHom V hTT']
      exact hT'
  refine Nat.card_congr ?_
  refine
    { toFun := fun γ => ⟨γ.1.map f.symm.toRingHom, (hfix' γ.1).mp γ.2.1, ?_⟩
      invFun := fun γ => ⟨γ.1.map f.toRingHom, (hfix γ.1).mp γ.2.1,
        (pres_iff _ _ _).mpr ((hpres γ.1 γ.2.1).mp ((pres_iff γ.1 γ.2.1 H).mp γ.2.2))⟩
      left_inv := fun γ => Subtype.ext ?_
      right_inv := fun γ => Subtype.ext ?_ }
  · have hγ' : (γ.1.map f.symm.toRingHom) • V = V := (hfix' γ.1).mp γ.2.1
    have e1 : (γ.1.map f.symm.toRingHom).map f.toRingHom = γ.1 := by
      rw [VariableChange.map_map]
      have : f.toRingHom.comp f.symm.toRingHom = RingHom.id L' := by
        ext x; exact f.apply_symm_apply x
      rw [this, VariableChange.map_id]
    rw [pres_iff _ hγ', hpres _ hγ']
    have key : ∀ (δ : VariableChange L') (hδ : δ • V.map f.toRingHom = V.map f.toRingHom)
        (heq : δ = γ.1), ∀ T ∈ H.map (mapPt f.toRingHom V), autPt δ hδ T ∈ H.map (mapPt f.toRingHom V) := by
      rintro δ hδ rfl
      exact (pres_iff γ.1 γ.2.1 _).mp γ.2.2
    exact key _ _ e1
  · show (γ.1.map f.symm.toRingHom).map f.toRingHom = γ.1
    rw [VariableChange.map_map]
    have : f.toRingHom.comp f.symm.toRingHom = RingHom.id L' := by
      ext x; exact f.apply_symm_apply x
    rw [this, VariableChange.map_id]
  · show (γ.1.map f.toRingHom).map f.symm.toRingHom = γ.1
    rw [VariableChange.map_map]
    have : f.symm.toRingHom.comp f.toRingHom = RingHom.id L := by
      ext x; exact f.symm_apply_apply x
    rw [this, VariableChange.map_id]

theorem natCard_stabSet_bot (V₀ : WeierstrassCurve L) :
    Nat.card (StabSet V₀ ⊥) = Nat.card (MulAction.stabilizer (VariableChange L) V₀) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨γ.1, γ.2.1⟩
      invFun := fun γ => ⟨γ.1, γ.2, fun T hT => ⟨0, (⊥ : AddSubgroup _).zero_mem, ?_⟩⟩
      left_inv := fun γ => rfl
      right_inv := fun γ => rfl }
  rw [(AddSubgroup.mem_bot).mp hT, Point.vcInvFun_zero]
  exact (castPt_eq_iff_heq γ.2 0 0).mp (castPt_zero γ.2)

theorem natCard_stabilizer_map_ringEquiv (f : L ≃+* L') (V : WeierstrassCurve L) :
    Nat.card (MulAction.stabilizer (VariableChange L') (V.map f.toRingHom)) =
      Nat.card (MulAction.stabilizer (VariableChange L) V) := by
  have hst := natCard_stabSet_map_ringEquiv f V ⊥
  rw [AddSubgroup.map_bot] at hst
  rw [← natCard_stabSet_bot V, ← hst]
  exact (natCard_stabSet_bot (V.map f.toRingHom)).symm

end StabTransport

section Residue

variable {K : Type*} [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]
  (W₀ : Place K M)

lemma bijective_algebraMap_residueField (hdeg : W₀.deg ≠ 0) :
    Function.Bijective (algebraMap K W₀.ResidueField) := by
  haveI : Module.Finite K W₀.ResidueField :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsIntegral K W₀.ResidueField := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

def resK (hdeg : W₀.deg ≠ 0) : W₀.ResidueField ≃+* K :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm

lemma resK_algebraMap (hdeg : W₀.deg ≠ 0) (c : K) :
    resK W₀ hdeg (algebraMap K W₀.ResidueField c) = c :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm_apply_apply c

lemma algebraMap_resK (hdeg : W₀.deg ≠ 0) (r : W₀.ResidueField) :
    algebraMap K W₀.ResidueField (resK W₀ hdeg r) = r :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).apply_symm_apply r

lemma ringHom_residueField_ext (hdeg : W₀.deg ≠ 0) {K' : Type*} [Field K']
    (φ φ' : W₀.ResidueField →+* K') (h : ∀ c : K, φ (algebraMap K _ c) = φ' (algebraMap K _ c)) :
    φ = φ' := by
  ext r
  obtain ⟨c, rfl⟩ := (bijective_algebraMap_residueField W₀ hdeg).2 r
  exact h c

lemma mem_maximalIdeal_of_ord_pos {f : M} (hf : 0 < W₀.ord f) :
    ∃ hfA : f ∈ W₀.toValuationSubring, (⟨f, hfA⟩ : W₀.toValuationSubring) ∈
      IsLocalRing.maximalIdeal W₀.toValuationSubring := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hf0 hπ
  have hn : W₀.ord f = (((W₀.ord f).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hf.le).symm
  have hn0 : (W₀.ord f).toNat ≠ 0 := by omega
  set a : W₀.toValuationSubring := (u : W₀.toValuationSubring) * π ^ (W₀.ord f).toNat with ha
  have hfa : f = (a : M) := by
    rw [hu, hn, zpow_natCast, ha]; push_cast; rfl
  refine ⟨hfa ▸ a.2, ?_⟩
  have : (⟨f, hfa ▸ a.2⟩ : W₀.toValuationSubring) = a := Subtype.ext hfa
  rw [this, ha]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hπ.maximalIdeal_eq ▸
    Ideal.mem_span_singleton_self π) _ (Nat.pos_of_ne_zero hn0))

end Residue

section ReduceAlong

variable {M Ω : Type*} [Field M] [Field Ω] [DecidableEq M] [DecidableEq Ω]
  {A : ValuationSubring M} {B : ValuationSubring Ω}
  [DecidableEq (ResidueField A)] [DecidableEq (ResidueField B)]
  (ι : M →+* Ω) (g : A →+* B) [IsLocalHom g] (hg : ∀ a : A, ((g a : B) : Ω) = ι a)
  (hcomap : ∀ x : M, ι x ∈ B → x ∈ A)

include hg in
theorem map_map_subtype_eq (W : WeierstrassCurve A) :
    (W.map g).map B.subtype = (W.map A.subtype).map ι := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  exact congrArg W.map (RingHom.ext fun a => hg a)

theorem map_map_residue_eq (W : WeierstrassCurve A) :
    (W.map g).map (residue B) = (W.map (residue A)).map (ResidueField.map g) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  exact congrArg W.map (RingHom.ext fun a => (ResidueField.map_residue g a).symm)

omit [DecidableEq Ω] [DecidableEq (ResidueField B)] [IsLocalHom g] in
theorem reduceHom_apply' {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : reduceHom hΔ P = reducePoint hΔ P := rfl

include hg hcomap in

theorem reduceHom_mapPt (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    (hΔ' : ((W.map g).map (residue B)).Δ ≠ 0)
    (hgen : (W.map g).map B.subtype = (W.map A.subtype).map ι)
    (hred : (W.map g).map (residue B) = (W.map (residue A)).map (ResidueField.map g))
    (P : (W.map A.subtype).toAffine.Point) :
    reduceHom hΔ' (castPt hgen.symm (mapPt ι _ P)) =
      castPt hred.symm (mapPt (ResidueField.map g) _ (reduceHom hΔ P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · show reduceHom hΔ' (castPt hgen.symm (mapPt ι _ 0)) =
      castPt hred.symm (mapPt (ResidueField.map g) _ (reduceHom hΔ 0))
    rw [mapPt_zero, castPt_zero, _root_.map_zero, _root_.map_zero, mapPt_zero, castPt_zero]
  · obtain ⟨hΩ, e1⟩ := mapPt_some ι (W.map A.subtype) h
    rw [e1]
    obtain ⟨hΩ', e2⟩ := castPt_some hgen.symm hΩ
    rw [e2, reduceHom_apply', reduceHom_apply']
    by_cases hx : x ∈ A
    · have hyA : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      have hX : ι x ∈ B := by rw [← hg ⟨x, hx⟩]; exact SetLike.coe_mem _
      rw [reducePoint_some_of_mem hΔ' hΩ' hX, reducePoint_some_of_mem hΔ h hx]
      obtain ⟨hk, e3⟩ := mapPt_some (ResidueField.map g) (W.map (residue A))
        (Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩) (y := ⟨y, hyA⟩) h.1)
      rw [e3]
      obtain ⟨hk', e4⟩ := castPt_some hred.symm hk
      rw [e4]
      apply some_congr
      · rw [ResidueField.map_residue]; exact congrArg _ (Subtype.ext (hg ⟨x, hx⟩).symm)
      · rw [ResidueField.map_residue]; exact congrArg _ (Subtype.ext (hg ⟨y, hyA⟩).symm)
    · have hX : ι x ∉ B := fun hX => hx (hcomap x hX)
      rw [reducePoint_some_of_notMem hΔ' hΩ' hX, reducePoint_some_of_notMem hΔ h hx, mapPt_zero,
        castPt_zero]

end ReduceAlong

section VeluMap

variable {L L' : Type*} [Field L] [Field L'] [DecidableEq L] [DecidableEq L']

omit [DecidableEq L] [DecidableEq L'] in
theorem map_veluGx (V : WeierstrassCurve L) (f : L →+* L') (x y : L) :
    (V.map f).veluGx (f x) (f y) = f (V.veluGx x y) := by
  simp only [veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

omit [DecidableEq L] [DecidableEq L'] in
theorem map_veluGy (V : WeierstrassCurve L) (f : L →+* L') (x y : L) :
    (V.map f).veluGy (f x) (f y) = f (V.veluGy x y) := by
  simp only [veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_mul, map_neg,
    map_ofNat]

omit [DecidableEq L] [DecidableEq L'] in
theorem map_veluQuotientOfSums (V : WeierstrassCurve L) (f : L →+* L') (t w : L) :
    (V.veluQuotientOfSums t w).map f = (V.map f).veluQuotientOfSums (f t) (f w) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp only [WeierstrassCurve.map_a₄, veluQuotientOfSums_a₄, map_sub, map_mul, map_ofNat]
  · simp only [WeierstrassCurve.map_a₆, veluQuotientOfSums_a₆, WeierstrassCurve.map_b₂, map_sub,
      map_mul, map_ofNat]

theorem coordsOrZero_mapPt (f : L →+* L') (V : WeierstrassCurve L) (P : V.toAffine.Point) :
    (mapPt f V P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show (mapPt f V 0).coordsOrZero = Prod.map f f (0, 0)
    rw [mapPt_zero]
    show ((0 : L'), (0 : L')) = (f 0, f 0)
    rw [_root_.map_zero]
  · obtain ⟨h', e⟩ := mapPt_some f V h
    rw [e]; rfl

theorem oddOrderSummingSet_mapPt (f : L →+* L') (V : WeierstrassCurve L) (Q : V.toAffine.Point) (n : ℕ) :
    (V.map f).oddOrderSummingSet (mapPt f V Q) n = (V.oddOrderSummingSet Q n).image (Prod.map f f) := by
  simp only [oddOrderSummingSet, Finset.image_image]
  congr 1
  ext k
  · show ((k • mapPt f V Q).coordsOrZero).1 = _
    rw [← map_nsmul, coordsOrZero_mapPt]; rfl
  · show ((k • mapPt f V Q).coordsOrZero).2 = _
    rw [← map_nsmul, coordsOrZero_mapPt]; rfl

theorem fullKernelQuotient_mapPt (f : L →+* L') (V : WeierstrassCurve L) (Q : V.toAffine.Point) (N : ℕ) :
    (V.map f).fullKernelQuotient (mapPt f V Q) N = (V.fullKernelQuotient Q N).map f := by
  have hinj : Function.Injective (Prod.map f f) := fun a b h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (f.injective h1) (f.injective h2)
  rw [fullKernelQuotient, fullKernelQuotient, oddOrderSummingSet_mapPt, map_veluQuotientOfSums,
    Finset.sum_image (hinj.injOn), Finset.sum_image (hinj.injOn), map_sum, map_sum]
  congr 1
  · exact Finset.sum_congr rfl fun P _ => map_veluGx V f P.1 P.2
  · refine Finset.sum_congr rfl fun P _ => ?_
    show f P.1 * (V.map f).veluGx (f P.1) (f P.2) - f P.2 * (V.map f).veluGy (f P.1) (f P.2) = _
    rw [map_veluGx, map_veluGy, map_sub, map_mul, map_mul]

end VeluMap

section LocalIncl

variable {M Ω : Type*} [Field M] [Field Ω] {A : ValuationSubring M} {B : ValuationSubring Ω}

def inclOfIff (ι : M →+* Ω) (hι : ∀ x, x ∈ A ↔ ι x ∈ B) : A →+* B where
  toFun a := ⟨ι a, (hι a).mp a.2⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' a b := Subtype.ext (map_mul ι (a : M) (b : M))
  map_zero' := Subtype.ext (map_zero ι)
  map_add' a b := Subtype.ext (map_add ι (a : M) (b : M))

theorem isLocalHom_inclOfIff (ι : M →+* Ω) (hι : ∀ x, x ∈ A ↔ ι x ∈ B) :
    IsLocalHom (inclOfIff ι hι) := by
  refine ⟨fun a ha => ?_⟩
  have ha0 : (a : M) ≠ 0 := by
    intro h
    have : (inclOfIff ι hι a : B) = 0 := Subtype.ext (by
      show ι a = 0
      rw [h, _root_.map_zero])
    exact ha.ne_zero this
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hb' : ι a * (b : Ω) = 1 := congrArg Subtype.val hb
  have hbinv : (b : Ω) = ι (a : M)⁻¹ := by
    rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hb').symm ▸ rfl
  have hainv : (a : M)⁻¹ ∈ A := (hι _).mpr (hbinv ▸ b.2)
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : M)⁻¹, hainv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem mem_of_isLocalHom (ι : M →+* Ω) (g : A →+* B) [IsLocalHom g]
    (hg : ∀ a : A, ((g a : B) : Ω) = ι a) (z : M) (hz : ι z ∈ B) : z ∈ A := by
  by_contra hzA
  have hz0 : z ≠ 0 := fun h => hzA (h ▸ A.zero_mem)
  have hzinv : z⁻¹ ∈ A := (A.mem_or_inv_mem z).resolve_left hzA
  have hnu' : (z⁻¹ : M) ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hzA)
  have hnu : ¬ IsUnit (⟨z⁻¹, hzinv⟩ : A) := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hnu') hu
  apply hnu
  apply IsUnit.of_map g
  refine IsUnit.of_mul_eq_one ⟨ι z, hz⟩ (Subtype.ext ?_)
  show ((g ⟨z⁻¹, hzinv⟩ : B) : Ω) * ι z = 1
  rw [hg]
  show ι z⁻¹ * ι z = 1
  rw [← map_mul, inv_mul_cancel₀ hz0, map_one]

end LocalIncl

section ResidueAlgebraic

variable {K M L : Type*} [Field K] [IsAlgClosed K] [Field M] [Field L] [Algebra K M] [Algebra M L]
  [Algebra.IsAlgebraic M L]

theorem mem_of_ord_nonneg (W₀ : Place K M) {f : M} (hf : f ≠ 0) (h : 0 ≤ W₀.ord f) :
    f ∈ W₀.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hf hπ
  rw [hu, show W₀.ord f = ((W₀.ord f).toNat : ℤ) by omega, zpow_natCast]
  exact mul_mem (SetLike.coe_mem _) (pow_mem π.2 _)

theorem bijective_residueField_comp (W₀ : Place K M) (hdeg : W₀.deg ≠ 0) {B : ValuationSubring L}
    (g : W₀.toValuationSubring →+* B) [IsLocalHom g]
    (hg : ∀ a, ((g a : B) : L) = algebraMap M L a) :
    Function.Bijective ((ResidueField.map g).comp (algebraMap K W₀.ResidueField)) := by
  classical
  let A := W₀.toValuationSubring
  let jK : K →+* ResidueField B := (ResidueField.map g).comp (algebraMap K W₀.ResidueField)
  show Function.Bijective jK
  apply IsAlgClosed.ringHom_bijective_of_isIntegral jK
  letI : Algebra K (ResidueField B) := jK.toAlgebra
  intro ξbar
  suffices h : IsAlgebraic K ξbar from h.isIntegral
  obtain ⟨ξ, rfl⟩ := IsLocalRing.residue_surjective ξbar
  obtain ⟨p, hp0, hpξ⟩ := Algebra.IsAlgebraic.isAlgebraic (R := M) (ξ : L)
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨i₀, hi₀, hmin⟩ := p.support.exists_min_image (fun i => W₀.ord (p.coeff i)) hsupp
  have hc0 : p.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  set c : M := (p.coeff i₀)⁻¹ with hc_def
  have hcoefA : ∀ i, c * p.coeff i ∈ A := by
    intro i
    by_cases hi : p.coeff i = 0
    · rw [hi, mul_zero]; exact A.zero_mem
    · have hisupp : i ∈ p.support := Polynomial.mem_support_iff.mpr hi
      apply mem_of_ord_nonneg W₀ (mul_ne_zero (inv_ne_zero hc0) hi)
      rw [W₀.ord_mul (inv_ne_zero hc0) hi, W₀.ord_inv]
      have := hmin i hisupp
      omega
  have hci₀ : c * p.coeff i₀ = 1 := inv_mul_cancel₀ hc0

  have heq : ∑ i ∈ p.support, (g ⟨c * p.coeff i, hcoefA i⟩) * ξ ^ i = 0 := by
    apply Subtype.ext
    push_cast
    simp only [hg]
    have h1 : ∑ i ∈ p.support, algebraMap M L (c * p.coeff i) * (ξ : L) ^ i =
        algebraMap M L c * Polynomial.aeval (ξ : L) p := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    exact_mod_cast (show ∑ i ∈ p.support, algebraMap M L (c * p.coeff i) * (ξ : L) ^ i = 0 by
      rw [h1, hpξ, mul_zero])

  let k : ℕ → K := fun i => resK W₀ hdeg (residue A ⟨c * p.coeff i, hcoefA i⟩)
  have hk : ∀ i, jK (k i) = residue B (g ⟨c * p.coeff i, hcoefA i⟩) := by
    intro i
    show ResidueField.map g (algebraMap K W₀.ResidueField (resK W₀ hdeg _)) = _
    rw [algebraMap_resK, ResidueField.map_residue]
  let q : Polynomial K := ∑ i ∈ p.support, Polynomial.C (k i) * Polynomial.X ^ i
  have hq0 : q ≠ 0 := by
    intro hq
    have h1 : q.coeff i₀ = k i₀ := by
      show (∑ i ∈ p.support, Polynomial.C (k i) * Polynomial.X ^ i).coeff i₀ = k i₀
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq p.support i₀ k, if_pos hi₀]
    have h2 : k i₀ = 1 := by
      show resK W₀ hdeg (residue A ⟨c * p.coeff i₀, hcoefA i₀⟩) = 1
      have : (⟨c * p.coeff i₀, hcoefA i₀⟩ : A) = 1 := Subtype.ext hci₀
      rw [this, map_one, map_one]
    rw [hq, Polynomial.coeff_zero] at h1
    exact one_ne_zero (h2.symm.trans h1.symm)
  refine ⟨q, hq0, ?_⟩
  show Polynomial.aeval (residue B ξ) (∑ i ∈ p.support, Polynomial.C (k i) * Polynomial.X ^ i) = 0
  rw [map_sum]
  simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  have h3 : ∀ i ∈ p.support, algebraMap K (ResidueField B) (k i) * residue B ξ ^ i =
      residue B (g ⟨c * p.coeff i, hcoefA i⟩ * ξ ^ i) := by
    intro i _
    rw [map_mul, map_pow, show algebraMap K (ResidueField B) (k i) = jK (k i) from rfl, hk]
  rw [Finset.sum_congr rfl h3, ← map_sum, heq, _root_.map_zero]

end ResidueAlgebraic

section Supplies

theorem isIntegral_of_apply_eq {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F]
    [Algebra K M] (x : F) (t : M) (ψ : F →ₐ[K] M) (hψ : ψ x = t)
    (halg : ∀ y : M, IsIntegral K⟮t⟯ y) : ψ.toRingHom.IsIntegral := by
  intro y
  obtain ⟨q, hqm, hq0⟩ := halg y
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

theorem j_congr {R : Type*} [CommRing R] {V₁ V₂ : WeierstrassCurve R} [V₁.IsElliptic] [V₂.IsElliptic]
    (h : V₁ = V₂) : V₁.j = V₂.j := by subst h; rfl

theorem isAddCyclic_card_zmultiples {G : Type*} [AddCommGroup G] (g : G) {N : ℕ} (hg : addOrderOf g = N) :
    IsAddCyclic (AddSubgroup.zmultiples g) ∧ Nat.card (AddSubgroup.zmultiples g) = N :=
  ⟨⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, hg]⟩

end Supplies

section Main

universe u v

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (M : Type v) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M]
    (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)]
    (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀))
    (W : WeierstrassCurve W₀.toValuationSubring)
    (hΔ : (W.map (residue W₀.toValuationSubring)).Δ ≠ 0)
    (hΔM : (W.map W₀.toValuationSubring.subtype).Δ ≠ 0)
    (hj : @WeierstrassCurve.j M _ (W.map W₀.toValuationSubring.subtype) ⟨isUnit_iff_ne_zero.mpr hΔM⟩ = t)
    (Q : (W.map W₀.toValuationSubring.subtype).toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔQ : ((W.map W₀.toValuationSubring.subtype).fullKernelQuotient Q N).Δ ≠ 0)
    (ψ : modularFunctionFieldFullC K N →ₐ[K] M)
    (hψj : ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t)
    (hψjN : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
      @WeierstrassCurve.j M _ ((W.map W₀.toValuationSubring.subtype).fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr hΔQ⟩) :
    W₀.ord (t - algebraMap K M j₀) *
        (Nat.card {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • W.map (residue W₀.toValuationSubring) = W.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
              HEq (Point.vcInvFun γ (W.map (residue W₀.toValuationSubring)).toAffine T) T'} : ℤ) =
      (Place.ramificationIndexAlong ψ W₀ : ℤ) *
        Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
          (W.map (residue W₀.toValuationSubring))) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)

  let A : ValuationSubring M := W₀.toValuationSubring
  let F := modularFunctionFieldFullC K N
  let jF : F := ⟨jqModC K, jqModC_mem_full K N⟩
  let jN : F := ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩
  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  have hdeg₀ : W₀.deg ≠ 0 := Place.deg_ne_zero_of_finiteDimensional_adjoin t ht W₀
  let Wt : WeierstrassCurve (ResidueField A) := W.map (residue A)
  let WM : WeierstrassCurve M := W.map A.subtype
  haveI hWtell : Wt.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI hWMell : WM.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔM⟩

  let rA : ResidueField A ≃+* K := resK W₀ hdeg₀
  let E₀ : WeierstrassCurve K := Wt.map rA.toRingHom
  haveI hE₀ell : E₀.IsElliptic := by
    show (Wt.map rA.toRingHom).IsElliptic; infer_instance
  have hE₀j : E₀.j = j₀ := by

    haveI hWell : W.IsElliptic := ⟨(map_residue_Δ_ne_zero_iff W).mp hΔ⟩
    have h1 : E₀.j = rA (residue A W.j) := by
      show (Wt.map rA.toRingHom).j = _
      rw [WeierstrassCurve.map_j, show Wt.j = residue A W.j from W.map_j (residue A)]; rfl
    have h2 : ((W.j : A) : M) = t := by
      rw [← hj]; exact (W.map_j A.subtype).symm
    obtain ⟨htjA, htj𝔪⟩ := mem_maximalIdeal_of_ord_pos W₀ hW₀
    have h3 : W.j - algebraMap K A j₀ ∈ IsLocalRing.maximalIdeal A := by
      have : W.j - algebraMap K A j₀ = ⟨t - algebraMap K M j₀, htjA⟩ := Subtype.ext (by
        push_cast; rw [h2]; rfl)
      rw [this]; exact htj𝔪
    rw [h1]
    have h4 : residue A W.j = residue A (algebraMap K A j₀) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact h3
    rw [h4]
    exact resK_algebraMap W₀ hdeg₀ j₀

  letI : DecidableEq K := Classical.decEq K
  obtain ⟨M₁, _iF₁, _iD₁, _iA₁, t₁, ht₁, hfin₁, hgal₁, hfull₁, hframe⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom K p N hN
  haveI := hfin₁
  haveI := hgal₁
  let tk₁ : K⟮t₁⟯ := ⟨t₁, IntermediateField.mem_adjoin_simple_self K t₁⟩
  let E' : WeierstrassCurve K⟮t₁⟯ := WeierstrassCurve.ofJ tk₁
  have hE'j : E'.j = tk₁ := WeierstrassCurve.ofJ_j tk₁

  let L := AlgebraicClosure M
  let e₁₀ : K⟮t₁⟯ ≃ₐ[K] K⟮t⟯ :=
    (RatFunc.algEquivOfTranscendental t₁ ht₁).symm.trans (RatFunc.algEquivOfTranscendental t ht)
  have he₁₀ : e₁₀ tk₁ = tk := by
    show RatFunc.algEquivOfTranscendental t ht ((RatFunc.algEquivOfTranscendental t₁ ht₁).symm tk₁) = tk
    rw [show tk₁ = IntermediateField.AdjoinSimple.gen K t₁ from rfl,
      RatFunc.algEquivOfTranscendental_symm_gen]
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X t ht
  letI algk₁M : Algebra K⟮t₁⟯ M := ((algebraMap K⟮t⟯ M).comp e₁₀.toAlgHom.toRingHom).toAlgebra
  have halgk₁M : ∀ x : K⟮t₁⟯, algebraMap K⟮t₁⟯ M x = ((e₁₀ x : K⟮t⟯) : M) := fun x => rfl
  haveI : IsScalarTower K K⟮t₁⟯ M := IsScalarTower.of_algebraMap_eq fun c => by
    rw [halgk₁M, e₁₀.commutes]; rfl
  have halgk₁L : ∀ x : K⟮t₁⟯, algebraMap K⟮t₁⟯ L x = algebraMap M L (algebraMap K⟮t₁⟯ M x) :=
    fun x => IsScalarTower.algebraMap_apply K⟮t₁⟯ M L x

  haveI hfink₁M : Module.Finite K⟮t₁⟯ M := by
    letI : Algebra K⟮t₁⟯ K⟮t⟯ := e₁₀.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower K⟮t₁⟯ K⟮t⟯ M := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Module.Finite K⟮t₁⟯ K⟮t⟯ := by
      refine Module.Finite.of_surjective (Algebra.linearMap K⟮t₁⟯ K⟮t⟯) ?_
      intro y; exact ⟨e₁₀.symm y, e₁₀.apply_symm_apply y⟩
    exact Module.Finite.trans K⟮t⟯ M
  haveI : Algebra.IsAlgebraic K⟮t₁⟯ L := Algebra.IsAlgebraic.trans K⟮t₁⟯ M L

  let ι₁ : M₁ →ₐ[K⟮t₁⟯] L := IsAlgClosed.lift
  let ι₁K : M₁ →ₐ[K] L := ι₁.restrictScalars K
  have hι₁t : ι₁ t₁ = algebraMap M L t := by
    have : ι₁ (algebraMap K⟮t₁⟯ M₁ tk₁) = algebraMap K⟮t₁⟯ L tk₁ := ι₁.commutes tk₁
    rw [show algebraMap K⟮t₁⟯ M₁ tk₁ = t₁ from rfl] at this
    rw [this, halgk₁L, halgk₁M, he₁₀]
  have hι₁inj : Function.Injective ι₁ := ι₁.toRingHom.injective

  haveI : Algebra.IsSeparable K⟮t₁⟯ M₁ := IsGalois.to_isSeparable
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K⟮t₁⟯ M₁
  let Ω : IntermediateField M L := M⟮ι₁ α⟯
  have hαint : IsIntegral M (ι₁ α) :=
    IsIntegral.tower_top ((Algebra.IsIntegral.isIntegral (R := K⟮t₁⟯) α).map ι₁)
  haveI hΩfin : FiniteDimensional M Ω := IntermediateField.adjoin.finiteDimensional hαint
  have hαsep : IsSeparable M (ι₁ α) :=
    IsSeparable.tower_top M (IsSeparable.map ι₁ hι₁inj (Algebra.IsSeparable.isSeparable K⟮t₁⟯ α))
  haveI hΩsep : Algebra.IsSeparable M Ω :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable M L).mpr hαsep

  have hι₁Ω : ∀ x : M₁, ι₁ x ∈ Ω := by
    intro x
    have hx : x ∈ (⊤ : IntermediateField K⟮t₁⟯ M₁) := IntermediateField.mem_top
    rw [← hα] at hx
    have h1 : (K⟮t₁⟯⟮α⟯).map ι₁ = K⟮t₁⟯⟮ι₁ α⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have h2 : K⟮t₁⟯⟮ι₁ α⟯ ≤ Ω.restrictScalars K⟮t₁⟯ := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact IntermediateField.mem_adjoin_simple_self M (ι₁ α)
    have h3 : ι₁ x ∈ (K⟮t₁⟯⟮α⟯).map ι₁ := ⟨x, hx, rfl⟩
    rw [h1] at h3
    exact h2 h3

  let ιΩ : M →ₐ[K] Ω := IsScalarTower.toAlgHom K M Ω
  have hιΩ : ∀ x : M, ((ιΩ x : Ω) : L) = algebraMap M L x := fun x => rfl
  let ι₁Ω : M₁ →ₐ[K] Ω :=
    { toFun := fun x => ⟨ι₁ x, hι₁Ω x⟩
      map_one' := Subtype.ext (map_one ι₁)
      map_mul' := fun x y => Subtype.ext (map_mul ι₁ x y)
      map_zero' := Subtype.ext (map_zero ι₁)
      map_add' := fun x y => Subtype.ext (map_add ι₁ x y)
      commutes' := fun c => Subtype.ext (by
        show ι₁K (algebraMap K M₁ c) = ((algebraMap K Ω c : Ω) : L)
        rw [ι₁K.commutes]
        rfl) }
  have hι₁Ωv : ∀ x : M₁, ((ι₁Ω x : Ω) : L) = ι₁ x := fun x => rfl

  have hιΩint : ιΩ.toRingHom.IsIntegral := fun y => Algebra.IsIntegral.isIntegral (R := M) y
  have hι₁Ωint : ι₁Ω.toRingHom.IsIntegral := by
    intro y
    haveI : Algebra.IsIntegral K⟮t₁⟯ L := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
    obtain ⟨q, hqm, hq0⟩ := Algebra.IsIntegral.isIntegral (R := K⟮t₁⟯) (y : L)
    refine ⟨q.map (algebraMap K⟮t₁⟯ M₁), hqm.map _, ?_⟩
    apply (algebraMap Ω L).injective
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, _root_.map_zero]
    have hc : ((algebraMap Ω L).comp ι₁Ω.toRingHom).comp (algebraMap K⟮t₁⟯ M₁) = algebraMap K⟮t₁⟯ L := by
      ext c
      show ι₁ (algebraMap K⟮t₁⟯ M₁ c) = algebraMap K⟮t₁⟯ L c
      exact ι₁.commutes c
    rw [hc]
    exact hq0

  have halgeq : (algebraAlong ιΩ : Algebra M Ω) = (inferInstance : Algebra M Ω) :=
    Algebra.algebra_ext _ _ fun r => rfl
  have hfinAlong : FiniteAlong K ιΩ := by
    unfold FiniteAlong; rw [halgeq]; exact hΩfin
  have hsepAlong : SeparableAlong K ιΩ := by
    unfold SeparableAlong; rw [halgeq]; exact hΩsep
  obtain ⟨Wbar, hWbar⟩ :=
    AlgebraicCurve.Place.restrictAlong_surjective ιΩ hιΩint hfinAlong hsepAlong W₀
  simp only at hWbar
  let W₁ : Place K M₁ := Wbar.restrictAlong ι₁Ω hι₁Ωint
  have hsame : ι₁Ω (t₁ - algebraMap K M₁ j₀) = ιΩ (t - algebraMap K M j₀) := by
    apply Subtype.ext
    rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes]
    show ι₁ t₁ - _ = algebraMap M L t - _
    rw [hι₁t]
  have hordbar : Wbar.ord (ιΩ (t - algebraMap K M j₀)) =
      Place.ramificationIndexAlong ιΩ Wbar * W₀.ord (t - algebraMap K M j₀) := by
    rw [Place.ord_restrictAlong ιΩ hιΩint Wbar, hWbar]
  have hordbar₁ : Wbar.ord (ιΩ (t - algebraMap K M j₀)) =
      Place.ramificationIndexAlong ι₁Ω Wbar * W₁.ord (t₁ - algebraMap K M₁ j₀) := by
    rw [← hsame, Place.ord_restrictAlong ι₁Ω hι₁Ωint Wbar]
  have hone : 1 ≤ Place.ramificationIndexAlong ιΩ Wbar :=
    Place.one_le_ramificationIndexAlong ιΩ hιΩint Wbar
  have hbarpos : 0 < Wbar.ord (ιΩ (t - algebraMap K M j₀)) := by
    rw [hordbar]; exact mul_pos (by exact_mod_cast hone) hW₀
  have hW₁ : 0 < W₁.ord (t₁ - algebraMap K M₁ j₀) := by
    rw [hordbar₁] at hbarpos
    exact pos_of_mul_pos_right hbarpos (by positivity)
  have hdeg₁ : W₁.deg ≠ 0 := Place.deg_ne_zero_of_finiteDimensional_adjoin t₁ ht₁ W₁

  letI : DecidableEq (ResidueField W₁.toValuationSubring) := Classical.decEq _
  obtain ⟨WA, κ₀, e₁, γ₀, hΔA, θ, ρ, hκ₀, hΔAu, he₁, hγ₀, hpin0, hpin1, hθinj, hρ, -, hequiv,
    hsurj, -⟩ := hframe j₀ E₀ hE₀j W₁ hW₁
  let A₁ : ValuationSubring M₁ := W₁.toValuationSubring

  haveI hE'ell : E'.IsElliptic := by
    show (WeierstrassCurve.ofJ tk₁).IsElliptic; infer_instance
  let E'M₁ : WeierstrassCurve M₁ := E'.baseChange M₁
  let E'L : WeierstrassCurve L := E'M₁.map ι₁.toRingHom
  let WL : WeierstrassCurve L := WM.map (algebraMap M L)
  haveI : E'M₁.IsElliptic := by
    show (E'.map (algebraMap K⟮t₁⟯ M₁)).IsElliptic; infer_instance
  haveI : E'L.IsElliptic := by
    show (E'M₁.map ι₁.toRingHom).IsElliptic; infer_instance
  haveI : WL.IsElliptic := by
    show (WM.map (algebraMap M L)).IsElliptic; infer_instance
  have hjWL : WL.j = algebraMap M L t := by
    rw [show WL.j = algebraMap M L WM.j from WM.map_j _, hj]
  have hjE'L : E'L.j = algebraMap M L t := by
    rw [show E'L.j = ι₁.toRingHom E'M₁.j from E'M₁.map_j _,
      show E'M₁.j = algebraMap K⟮t₁⟯ M₁ E'.j from E'.map_j _, hE'j]
    exact hι₁t
  obtain ⟨lam, hlam⟩ := WeierstrassCurve.exists_variableChange_of_j_eq WL E'L (hjWL.trans hjE'L.symm)
  have hlam' : (lam • WL).toAffine = E'L.toAffine := hlam

  have hNL : (N : L) ≠ 0 := by
    rw [show (N : L) = algebraMap K L N by simp]; exact (map_ne_zero _).mpr hN
  have hNM₁ : (N : M₁) ≠ 0 := by
    rw [show (N : M₁) = algebraMap K M₁ N by simp]; exact (map_ne_zero _).mpr hN
  let Q_L : WL.toAffine.Point := mapPt (algebraMap M L) WM Q
  have hQ_Lord : addOrderOf Q_L = N := by
    rw [← hQ]; exact addOrderOf_injective (mapPt (algebraMap M L) WM) (mapPt_injective _ _) Q
  let vlam : WL.toAffine.Point →+ E'L.toAffine.Point :=
    (castPt hlam).toAddMonoidHom.comp
      (AddMonoidHom.mk' (Point.vcInvFun lam WL.toAffine) (Point.vcInvFun_add lam WL.toAffine))
  have hvlam : ∀ P, vlam P = castPt hlam (Point.vcInvFun lam WL.toAffine P) := fun P => rfl
  have hvlam_inj : Function.Injective vlam := fun P P' h =>
    (Point.vcFun_rightInverse (C := lam) (W := WL.toAffine)).injective ((castPt hlam).injective h)
  let Q' : E'L.toAffine.Point := vlam Q_L
  have hQ'ord : addOrderOf Q' = N := by
    rw [← hQ_Lord]; exact addOrderOf_injective vlam hvlam_inj Q_L

  have hcardL : Nat.card {P : E'L.toAffine.Point // N • P = 0} ≤ N ^ 2 := by
    obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := L) (K := L) E'L hNL
    have hb : (E'L⁄L) = E'L.toAffine := by
      show (E'L.baseChange L).toAffine = E'L.toAffine
      rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hb] at eT
    have h1 : Nat.card (Submodule.torsionBy ℤ E'L.toAffine.Point N) = N ^ 2 := by
      rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
    have e2 : {P : E'L.toAffine.Point // N • P = 0} ≃ Submodule.torsionBy ℤ E'L.toAffine.Point N :=
      Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    rw [Nat.card_congr e2, h1]
  obtain ⟨Q_H, hQ_H⟩ : ∃ Q_H : E'M₁.toAffine.Point, mapPt ι₁.toRingHom E'M₁ Q_H = Q' := by
    let gt : {P : E'M₁.toAffine.Point // N • P = 0} → {P : E'L.toAffine.Point // N • P = 0} :=
      fun P => ⟨mapPt ι₁.toRingHom E'M₁ P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩
    have hgt : Function.Injective gt := fun P P' h =>
      Subtype.ext (mapPt_injective _ _ (congrArg Subtype.val h))
    haveI : Finite {P : E'M₁.toAffine.Point // N • P = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hfull₁]; exact pow_ne_zero _ hN0)
    haveI : Finite {P : E'L.toAffine.Point // N • P = 0} := by
      obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
        (F := L) (K := L) E'L hNL
      have hb : (E'L⁄L) = E'L.toAffine := by
        show (E'L.baseChange L).toAffine = E'L.toAffine
        rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      rw [hb] at eT
      have e2 : {P : E'L.toAffine.Point // N • P = 0} ≃ Submodule.torsionBy ℤ E'L.toAffine.Point N :=
        Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      haveI : Finite (ZMod N × ZMod N) := inferInstance
      exact Finite.of_equiv _ (eT.toEquiv.trans e2.symm)
    have hbij := hgt.bijective_of_nat_card_le (by rw [hfull₁]; exact hcardL)
    obtain ⟨P, hP⟩ := hbij.2 ⟨Q', by
      show N • Q' = 0
      rw [← hQ'ord]; exact addOrderOf_nsmul_eq_zero Q'⟩
    exact ⟨P.1, congrArg Subtype.val hP⟩
  have hQ_Hord : addOrderOf Q_H = N := by
    rw [← hQ'ord, ← hQ_H]
    exact (addOrderOf_injective (mapPt ι₁.toRingHom E'M₁) (mapPt_injective _ _) Q_H).symm
  have hΔQ_H : (E'M₁.fullKernelQuotient Q_H N).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N E'M₁ hNM₁ Q_H hQ_Hord
  have hΔQ_L : (WL.fullKernelQuotient Q_L N).Δ ≠ 0 :=
    WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N WL hNL Q_L hQ_Lord

  have hE'tr : Transcendental K E'.j := by
    rw [hE'j]
    intro halg
    exact ht₁ (by simpa using halg.algebraMap (A := M₁))
  obtain ⟨Φ₁, -, hΦ₁val⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
      K N hN K⟮t₁⟯ M₁ E' hE'tr hfull₁
  let H₁ : {H : AddSubgroup E'M₁.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
    ⟨AddSubgroup.zmultiples Q_H, isAddCyclic_card_zmultiples Q_H hQ_Hord⟩
  let ψ₁ : F →ₐ[K] M₁ := (Φ₁ H₁).1
  have hψ₁j : ψ₁ jF = t₁ := by
    have h : ψ₁ jF = algebraMap K⟮t₁⟯ M₁ E'.j := (Φ₁ H₁).2
    rw [h, hE'j]; rfl
  have hψ₁jN : ψ₁ jN = @WeierstrassCurve.j M₁ _ (E'M₁.fullKernelQuotient Q_H N)
      ⟨isUnit_iff_ne_zero.mpr hΔQ_H⟩ := hΦ₁val H₁ Q_H rfl hQ_Hord hΔQ_H

  have hY := ModularCurve.ord_mul_natCard_stabilizer_eq_ramificationIndexAlong_mul_of_equivariant_torsion_reduction
    K N hN j₀ E₀ M₁ t₁ ht₁ W₁ hW₁ θ ρ hfull₁ (fun P hP h0 => hθinj N P hpN hP h0) hρ hequiv hsurj
    Q_H hQ_Hord hΔQ_H ψ₁ hψ₁j hψ₁jN

  let ιL : M →ₐ[K] L := IsScalarTower.toAlgHom K M L
  have hjNeq : ι₁ (@WeierstrassCurve.j M₁ _ (E'M₁.fullKernelQuotient Q_H N) ⟨isUnit_iff_ne_zero.mpr hΔQ_H⟩) =
      algebraMap M L (@WeierstrassCurve.j M _ (WM.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔQ⟩) := by
    haveI i1 : (E'M₁.fullKernelQuotient Q_H N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔQ_H⟩
    haveI i2 : (WM.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔQ⟩
    haveI i3 : (WL.fullKernelQuotient Q_L N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔQ_L⟩
    have hV₁ : (E'M₁.fullKernelQuotient Q_H N).map ι₁.toRingHom = E'L.fullKernelQuotient Q' N := by
      rw [← fullKernelQuotient_mapPt, hQ_H]
    have hV₂ : (WM.fullKernelQuotient Q N).map (algebraMap M L) = WL.fullKernelQuotient Q_L N := by
      rw [← fullKernelQuotient_mapPt]
    have hV₃ : E'L.fullKernelQuotient Q' N = lam • WL.fullKernelQuotient Q_L N := by
      show E'L.fullKernelQuotient (castPt hlam (Point.vcInvFun lam WL.toAffine Q_L)) N = _
      rw [fullKernelQuotient_castPt,
        WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun WL lam Q_L hQ_Lord]
    calc ι₁ (E'M₁.fullKernelQuotient Q_H N).j
        = ((E'M₁.fullKernelQuotient Q_H N).map ι₁.toRingHom).j :=
          ((E'M₁.fullKernelQuotient Q_H N).map_j ι₁.toRingHom).symm
      _ = (lam • WL.fullKernelQuotient Q_L N).j := j_congr (hV₁.trans hV₃)
      _ = (WL.fullKernelQuotient Q_L N).j := variableChange_j _ _
      _ = ((WM.fullKernelQuotient Q N).map (algebraMap M L)).j := j_congr hV₂.symm
      _ = algebraMap M L (WM.fullKernelQuotient Q N).j := (WM.fullKernelQuotient Q N).map_j _
  have hψL : ι₁K.comp ψ₁ = ιL.comp ψ := by
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
    have htL : Transcendental K (algebraMap M L t) :=
      (transcendental_algebraMap_iff (algebraMap M L).injective).mpr ht
    obtain ⟨e17, he17⟩ :=
      ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental K N hN data
        L (algebraMap M L t) htL
    have h1 : (ι₁K.comp ψ₁) jF = algebraMap M L t := by
      show ι₁ (ψ₁ jF) = _; rw [hψ₁j, hι₁t]
    have h2 : (ιL.comp ψ) jF = algebraMap M L t := by
      show algebraMap M L (ψ jF) = _; rw [hψj]
    have hv : (ι₁K.comp ψ₁) jN = (ιL.comp ψ) jN := by
      show ι₁ (ψ₁ jN) = algebraMap M L (ψ jN)
      rw [hψ₁jN, hψjN]
      exact hjNeq
    have h3 : e17 ⟨_, h1⟩ = e17 ⟨_, h2⟩ := by
      apply Subtype.ext
      rw [he17, he17]
      exact hv
    exact congrArg Subtype.val (e17.injective h3)
  have hcompeq : ι₁Ω.comp ψ₁ = ιΩ.comp ψ := by
    apply AlgHom.ext; intro x; apply Subtype.ext
    exact congrArg (fun φ : F →ₐ[K] L => φ x) hψL

  have hint₀ : ψ.toRingHom.IsIntegral :=
    isIntegral_of_apply_eq jF t ψ hψj fun y => Algebra.IsIntegral.isIntegral y
  have hint₁ : ψ₁.toRingHom.IsIntegral :=
    isIntegral_of_apply_eq jF t₁ ψ₁ hψ₁j fun y => Algebra.IsIntegral.isIntegral y
  have hcompint : (ιΩ.comp ψ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hint₀ hιΩint
  have hcompint₁ : (ι₁Ω.comp ψ₁).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hint₁ hι₁Ωint
  have he₀ : Place.ramificationIndexAlong (ιΩ.comp ψ) Wbar =
      Place.ramificationIndexAlong ιΩ Wbar * Place.ramificationIndexAlong ψ W₀ := by
    rw [Place.ramificationIndexAlong_comp ψ ιΩ hint₀ hιΩint hcompint Wbar, hWbar]
  have he₁' : Place.ramificationIndexAlong (ιΩ.comp ψ) Wbar =
      Place.ramificationIndexAlong ι₁Ω Wbar * Place.ramificationIndexAlong ψ₁ W₁ := by
    rw [← hcompeq, Place.ramificationIndexAlong_comp ψ₁ ι₁Ω hint₁ hι₁Ωint hcompint₁ Wbar]

  have hS : Nat.card {γ : VariableChange K // γ • E₀ = E₀ ∧
      ∀ T ∈ AddSubgroup.zmultiples (θ Q_H), ∃ T' ∈ AddSubgroup.zmultiples (θ Q_H),
        HEq (Point.vcInvFun γ E₀.toAffine T) T'} =
      Nat.card {γ : VariableChange (ResidueField A) // γ • Wt = Wt ∧
        ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
          ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
            HEq (Point.vcInvFun γ Wt.toAffine T) T'} := by

    let Abar : ValuationSubring Ω := Wbar.toValuationSubring
    have hAĀ : ∀ x : M, x ∈ A ↔ ιΩ x ∈ Abar := by
      intro x
      have h : x ∈ (Wbar.restrictAlong ιΩ hιΩint).toValuationSubring ↔ ιΩ x ∈ Wbar.toValuationSubring :=
        Iff.rfl
      rw [hWbar] at h
      exact h
    have hA₁Ā : ∀ x : M₁, x ∈ A₁ ↔ ι₁Ω x ∈ Abar := fun x => Iff.rfl
    obtain ⟨AL, hO, hloc⟩ :=
      IsLocalRing.exists_factor_valuationRing ((algebraMap Ω L).comp Abar.subtype)
    let gĀ : Abar →+* AL := ((algebraMap Ω L).comp Abar.subtype).codRestrict AL hO
    haveI hgĀloc : IsLocalHom gĀ := ⟨fun a ha => hloc.map_nonunit a ha⟩
    let gA₀ : A →+* Abar := inclOfIff ιΩ.toRingHom hAĀ
    haveI : IsLocalHom gA₀ := isLocalHom_inclOfIff _ _
    let gA : A →+* AL := gĀ.comp gA₀
    have hgA : ∀ a : A, ((gA a : AL) : L) = algebraMap M L a := fun a => rfl
    let g₁₀ : A₁ →+* Abar := inclOfIff ι₁Ω.toRingHom hA₁Ā
    haveI : IsLocalHom g₁₀ := isLocalHom_inclOfIff _ _
    let g₁ : A₁ →+* AL := gĀ.comp g₁₀
    have hg₁ : ∀ a : A₁, ((g₁ a : AL) : L) = ι₁ a := fun a => rfl
    have hcomapA : ∀ z : M, algebraMap M L z ∈ AL → z ∈ A :=
      mem_of_isLocalHom (algebraMap M L) gA hgA
    have hcomapA₁ : ∀ z : M₁, ι₁.toRingHom z ∈ AL → z ∈ A₁ :=
      mem_of_isLocalHom ι₁.toRingHom g₁ hg₁

    have hbijL := bijective_residueField_comp (L := L) W₀ hdeg₀ gA hgA
    let jK : K →+* ResidueField AL := (ResidueField.map gA).comp (algebraMap K W₀.ResidueField)
    let rL : ResidueField AL ≃+* K := (RingEquiv.ofBijective jK hbijL).symm
    have hrLjK : ∀ c, rL (jK c) = c := (RingEquiv.ofBijective jK hbijL).symm_apply_apply
    let φA : ResidueField A →+* ResidueField AL := ResidueField.map gA
    let φA₁ : ResidueField A₁ →+* ResidueField AL := ResidueField.map g₁
    have hrφA : rL.toRingHom.comp φA = rA.toRingHom :=
      ringHom_residueField_ext W₀ hdeg₀ _ _ fun c => by
        show rL (jK c) = rA (algebraMap K _ c)
        rw [hrLjK]; exact (resK_algebraMap W₀ hdeg₀ c).symm
    have hjK₁ : ∀ c : K, φA₁ (algebraMap K (ResidueField A₁) c) = jK c := by
      intro c
      show ResidueField.map g₁ (residue A₁ (algebraMap K A₁ c)) =
        ResidueField.map gA (residue A (algebraMap K A c))
      rw [ResidueField.map_residue, ResidueField.map_residue]
      congr 1
      apply Subtype.ext
      show ι₁K (algebraMap K M₁ c) = algebraMap M L (algebraMap K M c)
      rw [ι₁K.commutes, ← IsScalarTower.algebraMap_apply]
    have hrφA₁ : rL.toRingHom.comp φA₁ = e₁.toRingHom :=
      ringHom_residueField_ext W₁ hdeg₁ _ _ fun c => by
        show rL (φA₁ (algebraMap K _ c)) = e₁ (algebraMap K _ c)
        rw [he₁, hjK₁, hrLjK]
    have hrφA' : ∀ x, rL.toRingHom (φA x) = rA.toRingHom x := fun x => RingHom.congr_fun hrφA x
    have hrφA₁' : ∀ x, rL.toRingHom (φA₁ x) = e₁.toRingHom x := fun x => RingHom.congr_fun hrφA₁ x

    have hΔunit : IsUnit W.Δ := (map_residue_Δ_ne_zero_iff W).mp hΔ
    let W_L : WeierstrassCurve AL := W.map gA
    let WA_L : WeierstrassCurve AL := WA.map g₁
    have hΔ₁' : (W_L.map (residue AL)).Δ ≠ 0 :=
      (map_residue_Δ_ne_zero_iff W_L).mpr (by
        show IsUnit (W.map gA).Δ; rw [WeierstrassCurve.map_Δ]; exact hΔunit.map gA)
    have hΔ₂' : (WA_L.map (residue AL)).Δ ≠ 0 :=
      (map_residue_Δ_ne_zero_iff WA_L).mpr (by
        show IsUnit (WA.map g₁).Δ; rw [WeierstrassCurve.map_Δ]; exact hΔAu.map g₁)
    have hgenW : W_L.map AL.subtype = WM.map (algebraMap M L) :=
      map_map_subtype_eq (algebraMap M L) gA hgA W
    have hgenWA : WA_L.map AL.subtype = (WA.map A₁.subtype).map ι₁.toRingHom :=
      map_map_subtype_eq ι₁.toRingHom g₁ hg₁ WA
    have hredW : W_L.map (residue AL) = Wt.map φA := map_map_residue_eq gA W
    have hredWA : WA_L.map (residue AL) = (WA.map (residue A₁)).map φA₁ := map_map_residue_eq g₁ WA
    let κL : VariableChange L := κ₀.map ι₁.toRingHom
    have hκL : κL • E'L = (WA.map A₁.subtype).map ι₁.toRingHom := by
      show (κ₀.map ι₁.toRingHom) • (E'M₁.map ι₁.toRingHom) = _
      rw [map_variableChange, hκ₀]
    let μ : VariableChange L := κL * lam
    have hμ : μ • W_L.map AL.subtype = WA_L.map AL.subtype := by
      rw [hgenW, hgenWA, mul_smul, ← hκL]
      show κL • (lam • WL) = κL • E'L
      rw [hlam]
    letI : DecidableEq (ResidueField AL) := Classical.decEq _
    obtain ⟨μ₀, -, hμ₀, hμt, hred⟩ :=
      WeierstrassCurve.exists_variableChange_map_eq_and_reduceHom_vcFun_eq (L := L) (A := AL)
        hΔ₁' hΔ₂' μ hμ

    let Q_Hκ : (WA.map A₁.subtype).toAffine.Point := castPt hκ₀ (Point.vcInvFun κ₀ E'M₁.toAffine Q_H)
    have hQ_Hκ : HEq (Point.vcInvFun κ₀ E'M₁.toAffine Q_H) Q_Hκ := heq_castPt hκ₀ _
    let R : (WA.map (residue A₁)).toAffine.Point := reduceHom hΔA Q_Hκ
    let Qt : Wt.toAffine.Point := reduceHom hΔ Q
    have c1 : reduceHom hΔ₁' (castPt hgenW.symm Q_L) = castPt hredW.symm (mapPt φA Wt Qt) :=
      reduceHom_mapPt (algebraMap M L) gA hgA hcomapA W hΔ hΔ₁' hgenW hredW Q
    have c2 : reduceHom hΔ₂' (castPt hgenWA.symm (mapPt ι₁.toRingHom (WA.map A₁.subtype) Q_Hκ)) =
        castPt hredWA.symm (mapPt φA₁ _ R) :=
      reduceHom_mapPt ι₁.toRingHom g₁ hg₁ hcomapA₁ WA hΔA hΔ₂' hgenWA hredWA Q_Hκ

    let P₂ : (WA_L.map AL.subtype).toAffine.Point :=
      castPt hgenWA.symm (mapPt ι₁.toRingHom (WA.map A₁.subtype) Q_Hκ)
    let P₀ : (μ • W_L.map AL.subtype).toAffine.Point :=
      Point.vcInvFun μ (W_L.map AL.subtype).toAffine (castPt hgenW.symm Q_L)
    have hPP₂ : castPt hμ P₀ = P₂ := by
      rcases hQdef : Q with _ | ⟨x, y, hxy⟩
      ·
        have hQL0 : Q_L = 0 := by show mapPt _ _ Q = 0; rw [hQdef]; exact mapPt_zero _ _
        have hQ'0 : Q' = 0 := by show vlam Q_L = 0; rw [hQL0, _root_.map_zero]
        have hQH0 : Q_H = 0 :=
          mapPt_injective _ _ (hQ_H.trans (hQ'0.trans (mapPt_zero _ _).symm))
        have hQHκ0 : Q_Hκ = 0 := by
          show castPt hκ₀ (Point.vcInvFun κ₀ E'M₁.toAffine Q_H) = 0
          rw [hQH0, Point.vcInvFun_zero, castPt_zero]
        have hP₂0 : P₂ = 0 := by
          show castPt hgenWA.symm (mapPt ι₁.toRingHom (WA.map A₁.subtype) Q_Hκ) = 0
          rw [hQHκ0, mapPt_zero, castPt_zero]
        have hP₀0 : P₀ = 0 := by
          show Point.vcInvFun μ (W_L.map AL.subtype).toAffine (castPt hgenW.symm Q_L) = 0
          rw [hQL0, castPt_zero, Point.vcInvFun_zero]
        rw [hP₂0, hP₀0, castPt_zero]
      ·
        obtain ⟨h1, e1⟩ := mapPt_some (algebraMap M L) WM hxy
        have hQL : Q_L = .some (algebraMap M L x) (algebraMap M L y) h1 := by
          show mapPt _ _ Q = _; rw [hQdef, e1]
        obtain ⟨h2, e2⟩ := vcInvFun_some lam WL h1
        obtain ⟨h3, e3⟩ := castPt_some hlam h2
        have hQ' : Q' = .some (vcXInv lam (algebraMap M L x)) (vcYInv lam (algebraMap M L x)
            (algebraMap M L y)) h3 := by
          show vlam Q_L = _; rw [hvlam, hQL, e2, e3]

        obtain ⟨xH, yH, hH, hQHdef⟩ : ∃ xH yH hH, Q_H = .some xH yH hH := by
          rcases hQH : Q_H with _ | ⟨xH, yH, hH⟩
          · exfalso
            have : Q' = 0 := by rw [← hQ_H, hQH, mapPt_zero']
            rw [hQ'] at this; exact Point.some_ne_zero _ this
          · exact ⟨xH, yH, hH, rfl⟩
        obtain ⟨h4, e4⟩ := mapPt_some ι₁.toRingHom E'M₁ hH
        have hcoord : ι₁.toRingHom xH = vcXInv lam (algebraMap M L x) ∧
            ι₁.toRingHom yH = vcYInv lam (algebraMap M L x) (algebraMap M L y) := by
          have h := hQ_H
          rw [hQHdef, e4, hQ'] at h
          exact ⟨(Point.some.inj h).1, (Point.some.inj h).2⟩

        obtain ⟨h5, e5⟩ := vcInvFun_some κ₀ E'M₁ hH
        obtain ⟨h6, e6⟩ := castPt_some hκ₀ h5
        have hQHκ : Q_Hκ = .some (vcXInv κ₀ xH) (vcYInv κ₀ xH yH) h6 := by
          show castPt hκ₀ (Point.vcInvFun κ₀ E'M₁.toAffine Q_H) = _
          rw [hQHdef, e5, e6]
        obtain ⟨h7, e7⟩ := mapPt_some ι₁.toRingHom (WA.map A₁.subtype) h6
        obtain ⟨h8, e8⟩ := castPt_some hgenWA.symm h7
        have hP₂ : P₂ = .some (ι₁.toRingHom (vcXInv κ₀ xH)) (ι₁.toRingHom (vcYInv κ₀ xH yH)) h8 := by
          show castPt hgenWA.symm (mapPt ι₁.toRingHom (WA.map A₁.subtype) Q_Hκ) = _
          rw [hQHκ, e7, e8]

        obtain ⟨h9, e9⟩ := castPt_some hgenW.symm h1
        obtain ⟨h10, e10⟩ := vcInvFun_some μ (W_L.map AL.subtype) h9
        obtain ⟨h11, e11⟩ := castPt_some hμ h10
        have hP₀ : castPt hμ P₀ = .some (vcXInv μ (algebraMap M L x))
            (vcYInv μ (algebraMap M L x) (algebraMap M L y)) h11 := by
          show castPt hμ (Point.vcInvFun μ (W_L.map AL.subtype).toAffine (castPt hgenW.symm Q_L)) = _
          rw [hQL, e9, e10, e11]
        rw [hP₀, hP₂]
        apply some_congr
        · rw [map_vcXInv, hcoord.1, ← vcXInv_mul]
        · rw [map_vcYInv, hcoord.1, hcoord.2, ← vcYInv_mul]
    have hredeq := hred P₀ P₂ ((castPt_eq_iff_heq hμ P₀ P₂).mp hPP₂)
      (castPt hμt.symm (reduceHom hΔ₂' P₂)) (heq_castPt hμt.symm _).symm
    have hvc : Point.vcFun μ (W_L.map AL.subtype).toAffine P₀ = castPt hgenW.symm Q_L :=
      Point.vcFun_rightInverse (C := μ) (W := (W_L.map AL.subtype).toAffine) _
    rw [hvc, c1] at hredeq
    rw [show reduceHom hΔ₂' P₂ = castPt hredWA.symm (mapPt φA₁ _ R) from c2, castPt_castPt] at hredeq

    have hkey : castPt (hredWA.symm.trans hμt.symm) (mapPt φA₁ _ R) =
        Point.vcInvFun (μ₀.map (residue AL)) (W_L.map (residue AL)).toAffine
          (castPt hredW.symm (mapPt φA Wt Qt)) := by
      rw [hredeq]
      exact (Point.vcFun_leftInverse (C := μ₀.map (residue AL))
        (W := (W_L.map (residue AL)).toAffine) _).symm

    let μK : VariableChange K := (μ₀.map (residue AL)).map rL.toRingHom
    have hμK : μK • E₀ = (WA.map (residue A₁)).map e₁.toRingHom := by
      have h := congrArg (fun V : WeierstrassCurve (ResidueField AL) => V.map rL.toRingHom) hμt
      beta_reduce at h
      have hL : ((μ₀.map (residue AL)) • W_L.map (residue AL)).map rL.toRingHom = μK • E₀ := by
        rw [← map_variableChange, hredW, WeierstrassCurve.map_map, hrφA]
      have hR : (WA_L.map (residue AL)).map rL.toRingHom = (WA.map (residue A₁)).map e₁.toRingHom := by
        rw [hredWA, WeierstrassCurve.map_map, hrφA₁]
      rw [hL, hR] at h
      exact h
    let ν : VariableChange K := γ₀ * μK
    have hν : ν • E₀ = E₀ := by
      show (γ₀ * μK) • E₀ = E₀
      rw [mul_smul, hμK]; exact hγ₀
    let QtK : E₀.toAffine.Point := mapPt rA.toRingHom Wt Qt
    have hθQ : θ Q_H = autPt ν hν QtK := by
      rcases hQt : Qt with _ | ⟨xt, yt, hxyt⟩
      ·
        have hL0 : castPt hredW.symm (mapPt φA Wt Qt) = 0 := by
          rw [hQt, mapPt_zero', castPt_zero]
        rw [hL0, Point.vcInvFun_zero, AddEquiv.map_eq_zero_iff] at hkey
        have hR0 : R = 0 := mapPt_injective _ _ (by rw [hkey, mapPt_zero])
        have hθ0 : θ Q_H = 0 := hpin0 Q_H Q_Hκ hQ_Hκ hR0
        rw [hθ0]
        show (0 : E₀.toAffine.Point) = autPt ν hν (mapPt rA.toRingHom Wt Qt)
        rw [hQt, mapPt_zero', _root_.map_zero]
      ·
        obtain ⟨h1, e1⟩ := mapPt_some φA Wt hxyt
        obtain ⟨h2, e2⟩ := castPt_some hredW.symm h1
        obtain ⟨h3, e3⟩ := vcInvFun_some (μ₀.map (residue AL)) (W_L.map (residue AL)) h2
        rw [hQt, e1, e2, e3] at hkey

        obtain ⟨xR, yR, hR', hRdef⟩ : ∃ xR yR hR', R = .some xR yR hR' := by
          rcases hR : R with _ | ⟨xR, yR, hR'⟩
          · exfalso
            rw [hR, mapPt_zero', castPt_zero] at hkey
            exact Point.some_ne_zero _ hkey.symm
          · exact ⟨xR, yR, hR', rfl⟩
        obtain ⟨h4, e4⟩ := mapPt_some φA₁ (WA.map (residue A₁)) hR'
        obtain ⟨h5, e5⟩ := castPt_some (hredWA.symm.trans hμt.symm) h4
        rw [hRdef, e4, e5] at hkey
        have hcoordR : φA₁ xR = vcXInv (μ₀.map (residue AL)) (φA xt) ∧
            φA₁ yR = vcYInv (μ₀.map (residue AL)) (φA xt) (φA yt) :=
          ⟨(Point.some.inj hkey).1, (Point.some.inj hkey).2⟩

        obtain ⟨h6, hθ1⟩ := hpin1 Q_H Q_Hκ xR yR hR' hQ_Hκ hRdef
        rw [hθ1]

        obtain ⟨h7, e7⟩ := mapPt_some rA.toRingHom Wt hxyt
        have hQtK : QtK = .some (rA.toRingHom xt) (rA.toRingHom yt) h7 := by
          show mapPt rA.toRingHom Wt Qt = _; rw [hQt, e7]
        obtain ⟨h8, e8⟩ := autPt_some (V := E₀) ν hν h7
        rw [hQtK, e8]
        have hx : e₁ xR = vcXInv μK (rA.toRingHom xt) := by
          show e₁.toRingHom xR = _
          rw [← hrφA₁' xR, hcoordR.1, map_vcXInv, hrφA' xt]
        have hy : e₁ yR = vcYInv μK (rA.toRingHom xt) (rA.toRingHom yt) := by
          show e₁.toRingHom yR = _
          rw [← hrφA₁' yR, hcoordR.2, map_vcYInv, hrφA' xt, hrφA' yt]
        apply some_congr
        · rw [hx, ← vcXInv_mul]
        · rw [hx, hy, ← vcYInv_mul]

    have hzm : AddSubgroup.zmultiples (θ Q_H) =
        ((AddSubgroup.zmultiples Qt).map (mapPt rA.toRingHom Wt)).map (autPt ν hν) := by
      rw [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, hθQ]
    rw [hzm]
    exact (natCard_stabSet_map_autPt E₀ ν hν _).trans
      (natCard_stabSet_map_ringEquiv rA Wt (AddSubgroup.zmultiples Qt))
  have hAut : Nat.card (MulAction.stabilizer (VariableChange K) E₀) =
      Nat.card (MulAction.stabilizer (VariableChange (ResidueField A)) Wt) :=
    natCard_stabilizer_map_ringEquiv rA Wt

  rw [hS, hAut] at hY
  have h1 : (Place.ramificationIndexAlong ιΩ Wbar : ℤ) * W₀.ord (t - algebraMap K M j₀) =
      (Place.ramificationIndexAlong ι₁Ω Wbar : ℤ) * W₁.ord (t₁ - algebraMap K M₁ j₀) := by
    rw [← hordbar, hordbar₁]
  have h2 : ((Place.ramificationIndexAlong ιΩ Wbar : ℕ) : ℤ) * (Place.ramificationIndexAlong ψ W₀ : ℕ) =
      ((Place.ramificationIndexAlong ι₁Ω Wbar : ℕ) : ℤ) * (Place.ramificationIndexAlong ψ₁ W₁ : ℕ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← he₀, he₁']
  have hc : ((Place.ramificationIndexAlong ιΩ Wbar : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega)
  apply mul_left_cancel₀ hc
  linear_combination (Nat.card {γ : VariableChange (ResidueField A) // γ • Wt = Wt ∧
        ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
          ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
            HEq (Point.vcInvFun γ Wt.toAffine T) T'} : ℤ) * h1 +
    (Place.ramificationIndexAlong ι₁Ω Wbar : ℤ) * hY -
    (Nat.card (MulAction.stabilizer (VariableChange (ResidueField A)) Wt) : ℤ) * h2

end Main

end P2MKcIntrinsicRamif

end

open P2MKcIntrinsicRamif in
universe u v in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (M : Type v) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M]
    (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)]
    (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀))
    (W : WeierstrassCurve W₀.toValuationSubring)
    (hΔ : (W.map (residue W₀.toValuationSubring)).Δ ≠ 0)
    (hΔM : (W.map W₀.toValuationSubring.subtype).Δ ≠ 0)
    (hj : @WeierstrassCurve.j M _ (W.map W₀.toValuationSubring.subtype) ⟨isUnit_iff_ne_zero.mpr hΔM⟩ = t)
    (Q : (W.map W₀.toValuationSubring.subtype).toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔQ : ((W.map W₀.toValuationSubring.subtype).fullKernelQuotient Q N).Δ ≠ 0)
    (ψ : modularFunctionFieldFullC K N →ₐ[K] M)
    (hψj : ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t)
    (hψjN : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
      @WeierstrassCurve.j M _ ((W.map W₀.toValuationSubring.subtype).fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr hΔQ⟩) :
    W₀.ord (t - algebraMap K M j₀) *
        (Nat.card {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • W.map (residue W₀.toValuationSubring) = W.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := W) hΔ Q),
              HEq (Point.vcInvFun γ (W.map (residue W₀.toValuationSubring)).toAffine T) T'} : ℤ) =
      (Place.ramificationIndexAlong ψ W₀ : ℤ) *
        Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
          (W.map (residue W₀.toValuationSubring))) :=
  main K N hN j₀ M t ht W₀ hW₀ W hΔ hΔM hj Q hQ hΔQ ψ hψj hψjN

end S_ModularCurve_ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer
end P2MW
export P2MW.S_ModularCurve_ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer (solution)
