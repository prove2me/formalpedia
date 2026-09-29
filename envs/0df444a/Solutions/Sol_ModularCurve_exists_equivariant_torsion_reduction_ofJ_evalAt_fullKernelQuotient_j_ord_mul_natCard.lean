-- Prove2me | solution 1 for ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3aa6500b-b291-5589-b2e7-96b7c3d295b1

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
import Theorems.Thm_ModularCurve_ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer
import Theorems.Thm_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_variableChange_vcInvFun
import Theorems.Thm_WeierstrassCurve_map_fullKernelQuotient_mapPoint
import Theorems.Thm_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
import Theorems.Thm_ModularCurve_ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped IntermediateField

namespace VRGLUE

universe u

theorem fullKernelQuotient_congr {F : Type u} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    (P₁ : W₁.toAffine.Point) (P₂ : W₂.toAffine.Point) (hP : HEq P₁ P₂) (N : ℕ) :
    W₁.fullKernelQuotient P₁ N = W₂.fullKernelQuotient P₂ N := by
  subst h; cases hP; rfl

theorem addOrderOf_congr {F : Type u} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    (P₁ : W₁.toAffine.Point) (P₂ : W₂.toAffine.Point) (hP : HEq P₁ P₂) :
    addOrderOf P₁ = addOrderOf P₂ := by
  subst h; cases hP; rfl

theorem addOrderOf_vcInvFun {F : Type u} [Field F] [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) : addOrderOf (Point.vcInvFun C W.toAffine P) = addOrderOf P := by
  let φ : W.toAffine.Point →+ (C • W).toAffine.Point :=
    { toFun := Point.vcInvFun C W.toAffine, map_zero' := rfl, map_add' := Point.vcInvFun_add C W.toAffine }
  have hinj : Function.Injective φ := by
    intro a b h
    have h1 : (Point.variableChangeEquiv C W.toAffine).symm a = (Point.variableChangeEquiv C W.toAffine).symm b := h
    exact (Point.variableChangeEquiv C W.toAffine).symm.injective h1
  exact (addOrderOf_injective φ hinj P)

theorem addOrderOf_mapPoint {F k : Type*} [Field F] [Field k] [DecidableEq F] [DecidableEq k] (f : F →+* k)
    {W : WeierstrassCurve F} (P : W.toAffine.Point) : addOrderOf (mapPoint f P) = addOrderOf P := by
  let φ : W.toAffine.Point →+ (W.map f).toAffine.Point :=
    { toFun := mapPoint f, map_zero' := mapPoint_zero f, map_add' := mapPoint_add f }
  exact addOrderOf_injective φ (mapPoint_injective f) P

end VRGLUE

namespace VRGLUE

universe u

theorem j_congr {F : Type u} [Field F] {X Y : WeierstrassCurve F} (h : X = Y) (iX : X.IsElliptic) (iY : Y.IsElliptic) :
    @WeierstrassCurve.j F _ X iX = @WeierstrassCurve.j F _ Y iY := by
  subst h; rfl

theorem residueInv_eq {K M : Type u} [Field K] [Field M] [Algebra K M] (W₀ : Place K M)
    (e : ResidueField W₀.toValuationSubring ≃+* K)
    (he : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c)
    (y : ResidueField W₀.toValuationSubring) : W₀.residueInv y = e y := by
  have hy : algebraMap K (ResidueField W₀.toValuationSubring) (e y) = y :=
    e.injective (he (e y))
  conv_lhs => rw [← hy]
  exact W₀.residueInv_algebraMap (e y)

theorem VR_value {K : Type u} [Field K] [DecidableEq K] {M : Type u} [Field M] [DecidableEq M] [Algebra K M]
    (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)]
    {E : WeierstrassCurve M} {E₀ : WeierstrassCurve K}
    (WA : WeierstrassCurve W₀.toValuationSubring) (κ₀ : VariableChange M)
    (e : ResidueField W₀.toValuationSubring ≃+* K) (γ₀ : VariableChange K)
    (hΔ : (WA.map (residue W₀.toValuationSubring)).Δ ≠ 0)
    (θ : E.toAffine.Point →+ E₀.toAffine.Point)
    (hκ₀ : κ₀ • E = WA.map W₀.toValuationSubring.subtype)
    (he : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c)
    (hγ₀ : γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = E₀)
    (hθ0 : ∀ (P : E.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point),
        HEq (Point.vcInvFun κ₀ E.toAffine P) P₁ → reduceHom hΔ P₁ = 0 → θ P = 0)
    (hθsome : ∀ (P : E.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point)
        (x y : ResidueField W₀.toValuationSubring)
        (h : (WA.map (residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
        HEq (Point.vcInvFun κ₀ E.toAffine P) P₁ → reduceHom hΔ P₁ = Point.some x y h →
        ∃ h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (e x)) (vcYInv γ₀ (e x) (e y)), θ P = Point.some _ _ h')
    {N : ℕ} (hNK : (N : K) ≠ 0)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔq : (E.fullKernelQuotient Q N).Δ ≠ 0) (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0) :
    @WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩ ∈ W₀.toValuationSubring ∧
    W₀.evalAt (@WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩) =
      @WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩ := by
  subst hγ₀

  have htyp : (κ₀ • E).toAffine.Point = (WA.map W₀.toValuationSubring.subtype).toAffine.Point := by rw [hκ₀]
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point, HEq (Point.vcInvFun κ₀ E.toAffine Q) Q₁ :=
    ⟨cast htyp (Point.vcInvFun κ₀ E.toAffine Q), (cast_heq htyp _).symm⟩
  have hQ₁ord : addOrderOf Q₁ = N := by
    rw [← addOrderOf_congr hκ₀ _ _ hQ₁, addOrderOf_vcInvFun, hQ]
  have hNκ : (N : ResidueField W₀.toValuationSubring) ≠ 0 := by
    intro h
    apply hNK
    have := congrArg e h
    rwa [map_natCast, map_zero] at this
  have hred : addOrderOf (reduceHom hΔ Q₁) = N := addOrderOf_reduceHom_of_natCast_ne_zero hΔ hNκ hQ₁ord

  have hup : (WA.map W₀.toValuationSubring.subtype).fullKernelQuotient Q₁ N = κ₀ • E.fullKernelQuotient Q N := by
    rw [← fullKernelQuotient_congr hκ₀ _ _ hQ₁ N, fullKernelQuotient_variableChange_vcInvFun E κ₀ Q hQ]

  have hθQ : θ Q = Point.vcInvFun γ₀ ((WA.map (residue W₀.toValuationSubring)).map e.toRingHom).toAffine
      (mapPoint e.toRingHom (reduceHom hΔ Q₁)) := by
    rcases hr : reduceHom hΔ Q₁ with _ | ⟨x, y, h⟩
    · rw [hθ0 Q Q₁ hQ₁ hr]
      rfl
    · obtain ⟨h', hθ'⟩ := hθsome Q Q₁ x y h hQ₁ hr
      rw [hθ', mapPoint_some]
      rfl
  have hmapord : addOrderOf (mapPoint e.toRingHom (reduceHom hΔ Q₁)) = N := by
    rw [addOrderOf_mapPoint, hred]
  have hdown : (γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N =
      γ₀ • (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom) := by
    rw [hθQ, fullKernelQuotient_variableChange_vcInvFun _ γ₀ _ hmapord, map_fullKernelQuotient_mapPoint]

  have hΔ₀' : ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).Δ ≠ 0 := by
    intro h0
    apply hΔ₀
    rw [hdown, variableChange_Δ, map_Δ, h0, map_zero, mul_zero]

  obtain ⟨W', hW'M, hW'κ, hrest⟩ :=
    WeierstrassCurve.exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom hΔ N Q₁ hred
  obtain ⟨hΔ', hmem, hres⟩ := hrest hΔ₀'

  have hjup : @WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩ =
      @WeierstrassCurve.j M _ ((WA.map W₀.toValuationSubring.subtype).fullKernelQuotient Q₁ N) ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ := by
    rw [j_congr hup ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ (by rw [← hup]; exact ⟨isUnit_iff_ne_zero.mpr hΔ'⟩)]
    exact (@variableChange_j M _ (E.fullKernelQuotient Q N) κ₀ ⟨isUnit_iff_ne_zero.mpr hΔq⟩).symm
  refine ⟨hjup ▸ hmem, ?_⟩
  rw [W₀.evalAt_of_mem (hjup ▸ hmem), residueInv_eq W₀ e he]
  have hres' : residue W₀.toValuationSubring ⟨_, hjup ▸ hmem⟩ = @WeierstrassCurve.j (ResidueField W₀.toValuationSubring) _
      ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀'⟩ := by
    have : (⟨_, hjup ▸ hmem⟩ : W₀.toValuationSubring) = ⟨_, hmem⟩ := Subtype.ext hjup
    rw [this, hres]
  rw [hres']

  haveI hXE : ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ₀'⟩
  haveI hXmE : (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).IsElliptic :=
    ⟨by rw [map_Δ]; exact (isUnit_iff_ne_zero.mpr hΔ₀').map _⟩
  haveI hXgE : (γ₀ • ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).IsElliptic :=
    ⟨by rw [variableChange_Δ]; exact (Units.isUnit _).pow 12 |>.mul hXmE.1⟩
  calc e ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).j
      = e.toRingHom ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).j := rfl
    _ = (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).j :=
        (map_j _ e.toRingHom).symm
    _ = (γ₀ • ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).j :=
        (variableChange_j _ γ₀).symm
    _ = _ := j_congr hdown.symm _ _

end VRGLUE

namespace VRGLUE

theorem heq_zero_of_eq {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    HEq (Point.zero : W₁.toAffine.Point) (Point.zero : W₂.toAffine.Point) := by
  subst h; rfl

theorem heq_some_of_eq {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x₁ y₁ x₂ y₂ : F}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : W₁.toAffine.Nonsingular x₁ y₁} {h₂ : W₂.toAffine.Nonsingular x₂ y₂} :
    HEq (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂) := by
  subst h; subst hx; subst hy; rfl

theorem ord_pos_of_residue_eq_zero {K M : Type*} [Field K] [Field M] [Algebra K M] (v : Place K M)
    {x : M} (hx : x ∈ v.toValuationSubring) (hx0 : x ≠ 0) (hres : residue v.toValuationSubring ⟨x, hx⟩ = 0) :
    0 < v.ord x := by
  have h0 : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp hx
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hinv : x⁻¹ ∈ v.toValuationSubring := by
      rw [v.mem_iff_ord_nonneg (inv_ne_zero hx0), v.ord_inv, ← h, neg_zero]
    have hunit : IsUnit (⟨x, hx⟩ : v.toValuationSubring) :=
      ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _ |>.mpr hunit) hres

theorem natCard_stabilizer_smul_map {κ K : Type*} [Field κ] [Field K] (e : κ ≃+* K) (γ : VariableChange K)
    (X : WeierstrassCurve κ) :
    Nat.card (MulAction.stabilizer (VariableChange K) (γ • X.map e.toRingHom)) =
      Nat.card (MulAction.stabilizer (VariableChange κ) X) := by
  classical

  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.card_map_of_injective (MulAut.conj γ).injective]

  let f : VariableChange κ →* VariableChange K := VariableChange.mapHom e.toRingHom
  let g : VariableChange K →* VariableChange κ := VariableChange.mapHom e.symm.toRingHom
  have hgf : ∀ C, g (f C) = C := by
    intro C
    show (C.map e.toRingHom).map e.symm.toRingHom = C
    ext <;> simp [VariableChange.map]
  have hfg : ∀ C, f (g C) = C := by
    intro C
    show (C.map e.symm.toRingHom).map e.toRingHom = C
    ext <;> simp [VariableChange.map]
  let F : MulAction.stabilizer (VariableChange κ) X ≃ MulAction.stabilizer (VariableChange K) (X.map e.toRingHom) :=
    { toFun := fun C => ⟨f C.1, by
        have h := C.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        show (C.1.map e.toRingHom) • X.map e.toRingHom = X.map e.toRingHom
        rw [map_variableChange, h]⟩
      invFun := fun C => ⟨g C.1, by
        have h := C.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        have h2 : (C.1.map e.symm.toRingHom) • (X.map e.toRingHom).map e.symm.toRingHom = (X.map e.toRingHom).map e.symm.toRingHom := by
          rw [map_variableChange, h]
        have hX : (X.map e.toRingHom).map e.symm.toRingHom = X := by
          rw [WeierstrassCurve.map_map]
          convert WeierstrassCurve.map_id X
          ext x; simp
        rw [hX] at h2
        exact h2⟩
      left_inv := fun C => Subtype.ext (hgf C.1)
      right_inv := fun C => Subtype.ext (hfg C.1) }
  exact (Nat.card_congr F).symm

theorem jqNModC_ne_algebraMap (K : Type*) [Field K] (N : ℕ) [NeZero N] (c : K) :
    (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N) ≠
      algebraMap K (modularFunctionFieldFullC K N) c := by
  intro h
  have h1 : (jqNModC K N : LaurentSeries K) = algebraMap K (LaurentSeries K) c := congrArg Subtype.val h
  have h2 := congrArg HahnSeries.order h1
  rw [show jqNModC K N = qExpand K N (jqModC K) from rfl, order_qExpand, order_jqModC] at h2
  have h3 : (algebraMap K (LaurentSeries K) c).order = 0 := by
    have hC : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
      rw [HahnSeries.algebraMap_apply']
      simp [HahnSeries.ofPowerSeries_C]
    rw [hC]; exact HahnSeries.order_C
  rw [h3] at h2
  have : (N : ℤ) = 0 := by linarith
  exact (NeZero.ne N) (by exact_mod_cast this)

end VRGLUE

namespace VRGLUE

universe u

theorem VR_order (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (M : Type u) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M]
    (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)]
    (j₀ : K) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀))
    {E : WeierstrassCurve M} {E₀ : WeierstrassCurve K}
    (WA : WeierstrassCurve W₀.toValuationSubring) (κ₀ : VariableChange M)
    (e : ResidueField W₀.toValuationSubring ≃+* K) (γ₀ : VariableChange K)
    (hΔ : (WA.map (residue W₀.toValuationSubring)).Δ ≠ 0)
    (θ : E.toAffine.Point →+ E₀.toAffine.Point)
    (hκ₀ : κ₀ • E = WA.map W₀.toValuationSubring.subtype)
    (he : ∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c)
    (hγ₀ : γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = E₀)
    (hθ0 : ∀ (P : E.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point),
        HEq (Point.vcInvFun κ₀ E.toAffine P) P₁ → reduceHom hΔ P₁ = 0 → θ P = 0)
    (hθsome : ∀ (P : E.toAffine.Point) (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point)
        (x y : ResidueField W₀.toValuationSubring)
        (h : (WA.map (residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
        HEq (Point.vcInvFun κ₀ E.toAffine P) P₁ → reduceHom hΔ P₁ = Point.some x y h →
        ∃ h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (e x)) (vcYInv γ₀ (e x) (e y)), θ P = Point.some _ _ h')
    (hEΔ : E.Δ ≠ 0) (hEj : @WeierstrassCurve.j M _ E ⟨isUnit_iff_ne_zero.mpr hEΔ⟩ = t)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = N)
    (hΔq : (E.fullKernelQuotient Q N).Δ ≠ 0) (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0)
    (ψ : modularFunctionFieldFullC K N →ₐ[K] M)
    (hψj : ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t)
    (hψjN : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
      @WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩) :
    W₀.ord (@WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩ -
        algebraMap K M (@WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩))
      * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) : ℤ) =
    W₀.ord (t - algebraMap K M j₀)
      * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) (E₀.fullKernelQuotient (θ Q) N)) : ℤ) := by
  subst hγ₀

  have htyp : (κ₀ • E).toAffine.Point = (WA.map W₀.toValuationSubring.subtype).toAffine.Point := by rw [hκ₀]
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point, HEq (Point.vcInvFun κ₀ E.toAffine Q) Q₁ :=
    ⟨cast htyp (Point.vcInvFun κ₀ E.toAffine Q), (cast_heq htyp _).symm⟩
  have hQ₁ord : addOrderOf Q₁ = N := by
    rw [← addOrderOf_congr hκ₀ _ _ hQ₁, addOrderOf_vcInvFun, hQ]
  have hNκ : (N : ResidueField W₀.toValuationSubring) ≠ 0 := by
    intro h
    apply hNK
    have := congrArg e h
    rwa [map_natCast, map_zero] at this
  have hred : addOrderOf (reduceHom hΔ Q₁) = N := addOrderOf_reduceHom_of_natCast_ne_zero hΔ hNκ hQ₁ord
  have hup : (WA.map W₀.toValuationSubring.subtype).fullKernelQuotient Q₁ N = κ₀ • E.fullKernelQuotient Q N := by
    rw [← fullKernelQuotient_congr hκ₀ _ _ hQ₁ N, fullKernelQuotient_variableChange_vcInvFun E κ₀ Q hQ]
  have hθQ : θ Q = Point.vcInvFun γ₀ ((WA.map (residue W₀.toValuationSubring)).map e.toRingHom).toAffine
      (mapPoint e.toRingHom (reduceHom hΔ Q₁)) := by
    rcases hr : reduceHom hΔ Q₁ with _ | ⟨x, y, h⟩
    · rw [hθ0 Q Q₁ hQ₁ hr]
      rfl
    · obtain ⟨h', hθ'⟩ := hθsome Q Q₁ x y h hQ₁ hr
      rw [hθ', mapPoint_some]
      rfl
  have hmapord : addOrderOf (mapPoint e.toRingHom (reduceHom hΔ Q₁)) = N := by
    rw [addOrderOf_mapPoint, hred]
  have hdown : (γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N =
      γ₀ • (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom) := by
    rw [hθQ, fullKernelQuotient_variableChange_vcInvFun _ γ₀ _ hmapord, map_fullKernelQuotient_mapPoint]
  have hΔ₀' : ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).Δ ≠ 0 := by
    intro h0
    apply hΔ₀
    rw [hdown, variableChange_Δ, map_Δ, h0, map_zero, mul_zero]
  obtain ⟨W', hW'M, hW'κ, hrest⟩ :=
    WeierstrassCurve.exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom hΔ N Q₁ hred
  obtain ⟨hΔ', hmem, hres⟩ := hrest hΔ₀'
  have hjup : @WeierstrassCurve.j M _ (E.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔq⟩ =
      @WeierstrassCurve.j M _ ((WA.map W₀.toValuationSubring.subtype).fullKernelQuotient Q₁ N) ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ := by
    rw [j_congr hup ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ (by rw [← hup]; exact ⟨isUnit_iff_ne_zero.mpr hΔ'⟩)]
    exact (@variableChange_j M _ (E.fullKernelQuotient Q N) κ₀ ⟨isUnit_iff_ne_zero.mpr hΔq⟩).symm

  have hj₀' : @WeierstrassCurve.j K _ ((γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩ =
      e (@WeierstrassCurve.j (ResidueField W₀.toValuationSubring) _
        ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀'⟩) := by
    haveI hXE : ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr hΔ₀'⟩
    haveI hXmE : (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).IsElliptic :=
      ⟨by rw [map_Δ]; exact (isUnit_iff_ne_zero.mpr hΔ₀').map _⟩
    symm
    calc e ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).j
        = e.toRingHom ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).j := rfl
      _ = (((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).j :=
          (map_j _ e.toRingHom).symm
      _ = (γ₀ • ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N).map e.toRingHom).j :=
          (variableChange_j _ γ₀).symm
      _ = _ := j_congr hdown.symm _ _

  haveI hEell : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hEΔ⟩
  have hΔM : (WA.map W₀.toValuationSubring.subtype).Δ ≠ 0 := by
    rw [← hκ₀, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hEΔ
  have hjWA : @WeierstrassCurve.j M _ (WA.map W₀.toValuationSubring.subtype) ⟨isUnit_iff_ne_zero.mpr hΔM⟩ = t := by
    rw [j_congr hκ₀.symm ⟨isUnit_iff_ne_zero.mpr hΔM⟩ inferInstance, variableChange_j]
    exact hEj
  have hψjN₁ : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
      @WeierstrassCurve.j M _ ((WA.map W₀.toValuationSubring.subtype).fullKernelQuotient Q₁ N) ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ :=
    hψjN.trans hjup
  have IR1 := ModularCurve.ord_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer
    K N hNK j₀ M t ht W₀ hW₀ WA hΔ hΔM hjWA Q₁ hQ₁ord hΔ' ψ hψj hψjN₁

  have hxmem : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∈ W₀.toValuationSubring := hψjN₁ ▸ hmem
  have hcmem : ∀ c : K, algebraMap K M c ∈ W₀.toValuationSubring := fun c => W₀.algebraMap_mem' c
  have hres_c : ∀ c : K, residue W₀.toValuationSubring ⟨algebraMap K M c, hcmem c⟩ =
      algebraMap K (ResidueField W₀.toValuationSubring) c := fun c => rfl
  have hx0 : ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ -
      algebraMap K M (@WeierstrassCurve.j K _ ((γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩) ≠ 0 := by
    intro h
    rw [sub_eq_zero, ← ψ.commutes] at h
    exact jqNModC_ne_algebraMap K N _ (ψ.toRingHom.injective h)
  set j' := @WeierstrassCurve.j K _ ((γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩ with hj'def
  have hW₀' : 0 < W₀.ord (ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ - algebraMap K M j') := by
    refine ord_pos_of_residue_eq_zero W₀ (sub_mem hxmem (hcmem j')) hx0 ?_
    have e1 : residue W₀.toValuationSubring ⟨ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ - algebraMap K M j', sub_mem hxmem (hcmem j')⟩ =
        residue W₀.toValuationSubring ⟨ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩, hxmem⟩ -
          residue W₀.toValuationSubring ⟨algebraMap K M j', hcmem j'⟩ := by
      rw [← map_sub]; rfl
    rw [e1, hres_c, hj₀', sub_eq_zero]
    have h1 : (⟨ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩, hxmem⟩ : W₀.toValuationSubring) = ⟨_, hmem⟩ :=
      Subtype.ext hψjN₁
    rw [h1, hres]

    exact (e.injective (he _)).symm
  have OJ := ModularCurve.ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient
    K N hNK j₀ M t ht W₀ hW₀ WA hΔ hΔM hjWA Q₁ hQ₁ord hΔ' ψ hψj hψjN₁ _ hW₀'

  haveI : (WA.map (residue W₀.toValuationSubring)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : Finite (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring)) (WA.map (residue W₀.toValuationSubring))) :=
    finite_stabilizer_variableChange _ _
  have hSpos : 0 < (Nat.card {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • WA.map (residue W₀.toValuationSubring) = WA.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
              HEq (Point.vcInvFun γ (WA.map (residue W₀.toValuationSubring)).toAffine T) T'} : ℤ) := by
    have hfin : Finite {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • WA.map (residue W₀.toValuationSubring) = WA.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
              HEq (Point.vcInvFun γ (WA.map (residue W₀.toValuationSubring)).toAffine T) T'} :=
      Finite.of_injective (fun γ => (⟨γ.1, γ.2.1⟩ : MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
        (WA.map (residue W₀.toValuationSubring)))) (fun a b h => Subtype.ext (by
          have h' := congrArg (fun z : MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
            (WA.map (residue W₀.toValuationSubring)) => (z : VariableChange (ResidueField W₀.toValuationSubring))) h
          exact h'))
    have hne : Nonempty {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • WA.map (residue W₀.toValuationSubring) = WA.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
              HEq (Point.vcInvFun γ (WA.map (residue W₀.toValuationSubring)).toAffine T) T'} :=
      ⟨⟨1, one_smul _ _, fun T hT => ⟨T, hT, by
        rcases T with _ | ⟨x, y, h⟩
        · exact heq_zero_of_eq (one_smul _ _)
        · exact heq_some_of_eq (one_smul _ _) (by simp [vcXInv, VariableChange.one_def]) (by simp [vcYInv, VariableChange.one_def])⟩⟩⟩
    exact_mod_cast Nat.card_pos
  have hepos : (Place.ramificationIndexAlong ψ W₀ : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at IR1
    exact (mul_pos hW₀ hSpos).ne' IR1

  have hA1 : Nat.card (MulAction.stabilizer (VariableChange K) (γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom)) =
      Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring)) (WA.map (residue W₀.toValuationSubring))) :=
    natCard_stabilizer_smul_map e γ₀ _
  have hA2 : Nat.card (MulAction.stabilizer (VariableChange K)
        ((γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom).fullKernelQuotient (θ Q) N)) =
      Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
        ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N)) := by
    rw [hdown]; exact natCard_stabilizer_smul_map e γ₀ _
  rw [hA1, hA2, ← hψjN]

  apply mul_left_cancel₀ hepos
  set a := W₀.ord (t - algebraMap K M j₀)
  set b := W₀.ord (ψ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ - algebraMap K M j')
  set ε := (Place.ramificationIndexAlong ψ W₀ : ℤ)
  set S := (Nat.card {γ : VariableChange (ResidueField W₀.toValuationSubring) //
          γ • WA.map (residue W₀.toValuationSubring) = WA.map (residue W₀.toValuationSubring) ∧
          ∀ T ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
            ∃ T' ∈ AddSubgroup.zmultiples (reduceHom (W := WA) hΔ Q₁),
              HEq (Point.vcInvFun γ (WA.map (residue W₀.toValuationSubring)).toAffine T) T'} : ℤ)
  set A₁ := (Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring)) (WA.map (residue W₀.toValuationSubring))) : ℤ)
  set A₂ := (Nat.card (MulAction.stabilizer (VariableChange (ResidueField W₀.toValuationSubring))
        ((WA.map (residue W₀.toValuationSubring)).fullKernelQuotient (reduceHom hΔ Q₁) N)) : ℤ)
  calc ε * (b * A₁) = b * (ε * A₁) := by ring
    _ = b * (a * S) := by rw [IR1]
    _ = a * (b * S) := by ring
    _ = a * (ε * A₂) := by rw [OJ]
    _ = ε * (a * A₂) := by ring

end VRGLUE

universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M j₀))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ p ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ = 1 → σ = 1) ∧

      (∀ (Q : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          addOrderOf Q = N →
          ∀ (hΔ : (((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N).Δ ≠ 0)
            (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0),
            @WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩ ∈ W₀.toValuationSubring ∧
            W₀.evalAt (@WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩) =
              @WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩) ∧

      (∀ (Q : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          addOrderOf Q = N →
          ∀ (hΔ : (((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N).Δ ≠ 0)
            (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0),
            W₀.ord (@WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩ -
                algebraMap K M (@WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩))
              * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) : ℤ) =
            W₀.ord (t - algebraMap K M j₀)
              * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K)
                  (E₀.fullKernelQuotient (θ Q) N)) : ℤ)) := by
  classical
  obtain ⟨M, instF, instD, instA, t, ht, instFD, instG, hfull, hframe⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom K p N hN
  letI := instF; letI := instD; letI := instA; letI := instFD; letI := instG

  obtain ⟨W₀, hW₀⟩ := AlgebraicCurve.Place.exists_ord_sub_algebraMap_pos_of_transcendental t ht j₀
  haveI : DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring) := Classical.decEq _
  obtain ⟨WA, κ₀, e, γ₀, hΔ, θ, ρ, hκ₀, hunit, he, hγ₀, hθ0, hθsome, hinj, hρ, hρmul, hequiv, hsurj, hfaith⟩ :=
    hframe j₀ E₀ hE₀ W₀ hW₀
  refine ⟨M, instF, instD, instA, t, ht, instFD, instG, W₀, hW₀, θ, ρ, hfull, hinj, hρ, hρmul, hequiv, hsurj, hfaith, ?_, ?_⟩
  ·
    intro Q hQ hΔq hΔ₀
    exact VRGLUE.VR_value W₀ WA κ₀ e γ₀ hΔ θ hκ₀ he hγ₀ hθ0 hθsome hN Q hQ hΔq hΔ₀
  ·
    intro Q hQ hΔq hΔ₀
    have htK : Transcendental K (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯) := by
      rw [← transcendental_algebraMap_iff (algebraMap K⟮t⟯ M).injective]
      exact ht
    have hEjt : Transcendental K (WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).j := by
      rw [WeierstrassCurve.ofJ_j]; exact htK
    obtain ⟨Φ, -, hΦ⟩ :=
      ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j K N hN K⟮t⟯ M
        (WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)) hEjt hfull
    let H : {H : AddSubgroup ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N} :=
      ⟨AddSubgroup.zmultiples Q, AddSubgroup.isAddCyclic_zmultiples Q, by rw [Nat.card_zmultiples, hQ]⟩
    have hψj : (Φ H).1 ⟨jqModC K, jqModC_mem_full K N⟩ = t := by
      rw [(Φ H).2, WeierstrassCurve.ofJ_j]; rfl
    have hψjN := hΦ H Q rfl hQ hΔq

    have hEΔ : ((WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).Δ ≠ 0 := by
      have h1 : (κ₀ • (WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).Δ ≠ 0 := by
        rw [hκ₀, WeierstrassCurve.map_Δ]
        intro h0
        exact hunit.ne_zero (Subtype.val_injective (by simpa using h0))
      intro h0
      apply h1
      rw [WeierstrassCurve.variableChange_Δ, h0, mul_zero]
    have hEj : @WeierstrassCurve.j M _ ((WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M)
        ⟨isUnit_iff_ne_zero.mpr hEΔ⟩ = t := by
      have h2 := @WeierstrassCurve.map_j K⟮t⟯ _ (WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯))
        inferInstance M _ (algebraMap K⟮t⟯ M)
      rw [WeierstrassCurve.ofJ_j] at h2
      exact (VRGLUE.j_congr rfl _ _).trans h2
    exact VRGLUE.VR_order K N hN M t ht W₀ j₀ hW₀ WA κ₀ e γ₀ hΔ θ hκ₀ he hγ₀ hθ0 hθsome hEΔ hEj Q hQ hΔq hΔ₀ (Φ H).1 hψj hψjN

end S_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
end P2MW
export P2MW.S_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard (solution)
