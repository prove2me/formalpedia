-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fa30ecc1-598d-5422-bb09-a11245faee75

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataPow
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
import Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Theorems.Thm_ModularCurve_map_coeffMap_tateLaurent
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single jq modularFunctionFieldFull qExpFunctionFieldC coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange mem_laurentBaseChange_iff FullLevel.levelH xHFunctionField LevelModuliPackageAbs RigidWeierstrassData RigidWeierstrassData.Rel RigidWeierstrassData.Rel.refl RigidWeierstrassData.Rel.trans kernelVariableChangeDeg kernelVariableChangeDeg_mul kernelVariableChangeDeg_map LevelPData IsLevelPStructure tateLaurent gamma0PowDeg IsGamma0PowAt tateBase toricPoint cuspPoint cuspData cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot toricPoint_level_mul map_coeffMap_tateLaurent transcendental_jqNModC qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace Gamma0PowLayerAssembly
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq~coeffEmb_qExpand~coeffMap_injective~coeffMap_jqNModC"

p2m_open "WeierstrassCurve~cusp Polynomial ModularCurve~coeffMap_qExpand~coeffEmb_jq~coeffEmb_qExpand~coeffMap_injective~coeffMap_jqNModC P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve WeierstrassCurve.DrinfeldGlobal"

section PtCongr

variable {F : Type*} [Field F] [DecidableEq F]

noncomputable def ptCongr {W W' : WeierstrassCurve F} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem ptCongr_some {W W' : WeierstrassCurve F} (h : W = W') (x y : F) (hxy : W.toAffine.Nonsingular x y) :
    ptCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h; rfl

theorem exists_ptCongr_symm_eq_some {W W' : WeierstrassCurve F} (h : W = W') (x y : F)
    (hxy : W'.toAffine.Nonsingular x y) :
    ∃ hxy' : W.toAffine.Nonsingular x y, (ptCongr h).symm (.some x y hxy) = .some x y hxy' := by
  subst h; exact ⟨hxy, rfl⟩

theorem cyclicQuotientJ_map_ptCongr {W W' : WeierstrassCurve F} (h : W = W')
    (H : AddSubgroup W.toAffine.Point) (N : ℕ) :
    W'.cyclicQuotientJ (H.map (ptCongr h).toAddMonoidHom) N = W.cyclicQuotientJ H N := by
  subst h
  congr 1
  ext P
  simp [ptCongr]

end PtCongr

section VC

variable {F : Type*} [Field F] [DecidableEq F]

noncomputable def vcAddEquiv (C : VariableChange F) (W : WeierstrassCurve F) :
    (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  { (Affine.Point.variableChangeEquiv C W.toAffine) with
    map_add' := fun P Q => by
      have hinj : Function.Injective (Affine.Point.vcInvFun C W.toAffine) :=
        (Affine.Point.vcFun_rightInverse (C := C) (W := W.toAffine)).injective
      apply hinj
      change Affine.Point.vcInvFun C W.toAffine (Affine.Point.vcFun C W.toAffine (P + Q)) =
        Affine.Point.vcInvFun C W.toAffine (Affine.Point.vcFun C W.toAffine P + Affine.Point.vcFun C W.toAffine Q)
      rw [WeierstrassCurve.Affine.Point.vcInvFun_add, Affine.Point.vcFun_leftInverse,
        Affine.Point.vcFun_leftInverse, Affine.Point.vcFun_leftInverse] }

theorem vcAddEquiv_apply (C : VariableChange F) (W : WeierstrassCurve F) (P : (C • W).toAffine.Point) :
    vcAddEquiv C W P = Affine.Point.vcFun C W.toAffine P := rfl

theorem vcAddEquiv_some (C : VariableChange F) (W : WeierstrassCurve F) (x y : F)
    (h : (C • W).toAffine.Nonsingular x y) :
    vcAddEquiv C W (.some x y h) = .some (Affine.vcX C x) (Affine.vcY C x y)
      ((Affine.nonsingular_variableChange_iff x y).mp h) := rfl

theorem mem_zmultiples_iff_vcFun_mem (C : VariableChange F) (W : WeierstrassCurve F) (h P : (C • W).toAffine.Point) :
    P ∈ AddSubgroup.zmultiples h ↔
      Affine.Point.vcFun C W.toAffine P ∈ AddSubgroup.zmultiples (vcAddEquiv C W h) := by
  rw [← vcAddEquiv_apply, ← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.map_zmultiples,
    AddSubgroup.mem_map_iff_mem (vcAddEquiv C W).injective]

end VC

section CutOut

def IsCutOut {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (M' : ℕ)
    (h : ↥M'.primeFactors → F[X]) (g : W.toAffine.Point) : Prop :=
  addOrderOf g = M' ∧
    ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : F) (h₁ : W.toAffine.Nonsingular x₁ y₁),
      n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
      (h p).IsRoot x₁

theorem IsCutOut.map {F₁ F₂ : Type*} [Field F₁] [DecidableEq F₁] [Field F₂] [DecidableEq F₂]
    {W₁ : WeierstrassCurve F₁} {W₂ : WeierstrassCurve F₂}
    (f : W₁.toAffine.Point →+ W₂.toAffine.Point) (hf : Function.Injective f) (φ : F₁ → F₂)
    (hsome : ∀ (x y : F₁) (hxy : W₁.toAffine.Nonsingular x y),
      ∃ (y' : F₂) (hxy' : W₂.toAffine.Nonsingular (φ x) y'), f (.some x y hxy) = .some (φ x) y' hxy')
    {M' : ℕ} (h₁ : ↥M'.primeFactors → F₁[X]) (h₂ : ↥M'.primeFactors → F₂[X])
    (hroot : ∀ (p : ↥M'.primeFactors) (x : F₁), (h₁ p).IsRoot x → (h₂ p).IsRoot (φ x))
    {g : W₁.toAffine.Point} (hg : IsCutOut W₁ M' h₁ g) : IsCutOut W₂ M' h₂ (f g) := by
  refine ⟨by rw [addOrderOf_injective f hf, hg.1], ?_⟩
  intro p n x₂ y₂ hxy₂ hn hord
  rw [← map_nsmul] at hn hord
  rw [addOrderOf_injective f hf] at hord

  rcases hng : n • g with _ | ⟨x₁, y₁, hxy₁⟩
  · rw [hng, ← WeierstrassCurve.Affine.Point.zero_def, map_zero] at hn
    exact absurd hn.symm (WeierstrassCurve.Affine.Point.some_ne_zero hxy₂)
  · obtain ⟨y', hxy', hf'⟩ := hsome x₁ y₁ hxy₁
    rw [hng, hf'] at hn
    have hx : φ x₁ = x₂ := (WeierstrassCurve.Affine.Point.some.inj hn).1
    rw [← hx]
    exact hroot p x₁ (hg.2 p n x₁ y₁ hxy₁ hng hord)

theorem isRoot_of_isRoot_kernelVariableChangeDeg {F : Type*} [Field F] (C : VariableChange F) (d : ℕ)
    (h : F[X]) (x : F) (hx : (ModularCurve.kernelVariableChangeDeg C d h).IsRoot x) :
    h.IsRoot (WeierstrassCurve.Affine.vcX C x) := by
  rw [ModularCurve.kernelVariableChangeDeg, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exact absurd hx (pow_ne_zero _ (C.u⁻¹).ne_zero)
  · exact hx

end CutOut

section Group

variable {G : Type*} [AddCommGroup G]

theorem mem_of_ordCompl_nsmul_mem (H : AddSubgroup G) (g : G) (M : ℕ) (hM0 : M ≠ 0) (hM : M • g = 0)
    (h : ∀ p ∈ M.primeFactors, (M / p ^ M.factorization p) • g ∈ H) : g ∈ H := by

  rw [← QuotientAddGroup.eq_zero_iff]
  set gb : G ⧸ H := (g : G ⧸ H) with hgb
  have hordM : addOrderOf gb ∣ M := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [hgb, ← QuotientAddGroup.mk_nsmul, hM, QuotientAddGroup.mk_zero]
  have hordp : ∀ p ∈ M.primeFactors, addOrderOf gb ∣ M / p ^ M.factorization p := by
    intro p hp
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [hgb, ← QuotientAddGroup.mk_nsmul, (QuotientAddGroup.eq_zero_iff _).mpr (h p hp)]
  have hone : addOrderOf gb = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpM : p ∣ M := hpdvd.trans hordM
    have hpmem : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpM, hM0⟩
    exact Nat.not_dvd_ordCompl hp hM0 (hpdvd.trans (hordp p hpmem))
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

theorem addOrderOf_div_nsmul (g : G) (M d : ℕ) (hg : addOrderOf g = M) (hM0 : M ≠ 0) (hd : d ∣ M) :
    addOrderOf ((M / d) • g) = d := by
  subst hg
  exact addOrderOf_nsmul_addOrderOf_sub hM0 hd

end Group

section Tate

def TatePowTarget (F' : Type) [Field F'] (N₀ : ℕ) : Type := AlgebraicClosure (LaurentSeries F')

variable (F' : Type) [Field F'] (N₀ : ℕ)

noncomputable scoped instance : Field (TatePowTarget F' N₀) := inferInstanceAs (Field (AlgebraicClosure _))

scoped instance : IsAlgClosed (TatePowTarget F' N₀) := inferInstanceAs (IsAlgClosed (AlgebraicClosure _))

noncomputable scoped instance : DecidableEq (TatePowTarget F' N₀) := Classical.decEq _

noncomputable def TatePowTarget.incl : LaurentSeries F' →+* TatePowTarget F' N₀ :=
  algebraMap (LaurentSeries F') (AlgebraicClosure (LaurentSeries F'))

theorem TatePowTarget.incl_injective : Function.Injective (TatePowTarget.incl F' N₀) :=
  (algebraMap (LaurentSeries F') (AlgebraicClosure (LaurentSeries F'))).injective

noncomputable scoped instance [NeZero N₀] : Algebra (LaurentSeries F') (TatePowTarget F' N₀) :=
  ((TatePowTarget.incl F' N₀).comp (ModularCurve.qExpand F' N₀)).toAlgebra

theorem TatePowTarget.algebraMap_eq [NeZero N₀] :
    algebraMap (LaurentSeries F') (TatePowTarget F' N₀) = (TatePowTarget.incl F' N₀).comp (ModularCurve.qExpand F' N₀) :=
  rfl

theorem TatePowTarget.algebraMap_apply [NeZero N₀] (x : LaurentSeries F') :
    algebraMap (LaurentSeries F') (TatePowTarget F' N₀) x = TatePowTarget.incl F' N₀ (ModularCurve.qExpand F' N₀ x) :=
  rfl

scoped instance TatePowTarget.charZero [CharZero F'] : CharZero (TatePowTarget F' N₀) := by
  haveI : CharZero (LaurentSeries F') :=
    charZero_of_injective_ringHom (f := (HahnSeries.C : F' →+* LaurentSeries F')) HahnSeries.C_injective
  exact charZero_of_injective_ringHom (TatePowTarget.incl_injective F' N₀)

p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget"
variable {F' N₀}

end Tate
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget"

section TateSide

variable {F' : Type} [Field F'] {N₀ : ℕ} [NeZero N₀] {Ω' : Type} [Field Ω'] [DecidableEq Ω']
  [Algebra (LaurentSeries F') Ω'] (incl : LaurentSeries F' →+* Ω')
  (halg : ∀ y, algebraMap (LaurentSeries F') Ω' y = incl (ModularCurve.qExpand F' N₀ y))

include halg in

theorem incl_toricPoint_fst (c : F') :
    incl (ModularCurve.toricPoint F' N₀ c).1 =
      algebraMap (LaurentSeries F') Ω' (ModularCurve.toricPoint F' 1 c).1 := by
  have key := ModularCurve.toricPoint_level_mul F' 1 N₀ c
  rw [mul_one] at key
  rw [halg, key]

include halg in
theorem cyclicQuotientJ_zmultiples_eq_of_toric (M' : ℕ) [NeZero M'] (ζ : F') (hζ : IsPrimitiveRoot ζ M')
    (g : ((ModularCurve.tateLaurent F').baseChange (Ω')).toAffine.Point)
    (hgord : addOrderOf g = M')
    (hcut : ∀ p ∈ M'.primeFactors, ∀ (n : ℕ) (X Y : Ω')
      (hXY : ((ModularCurve.tateLaurent F').baseChange (Ω')).toAffine.Nonsingular X Y),
      n • g = .some X Y hXY → addOrderOf (n • g) = p ^ M'.factorization p →
        ∃ a ∈ (Finset.Icc 1 (p ^ M'.factorization p / 2)).filter (fun a => ¬ p ∣ a),
          X = incl (ModularCurve.toricPoint F' N₀ ((ζ ^ (M' / p ^ M'.factorization p)) ^ a)).1)
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    ((ModularCurve.tateLaurent F').baseChange (Ω')).cyclicQuotientJ
        (AddSubgroup.zmultiples ((M' / d) • g)) d =
      incl (ModularCurve.qExpand F' N₀ (ModularCurve.jqNModC F' d)) := by
  have hM'0 : M' ≠ 0 := NeZero.ne M'

  obtain ⟨P, hP0, hP⟩ : ∃ P : ((ModularCurve.tateLaurent F').baseChange (Ω')).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ M' ∣ n) ∧
      ∀ n : ℕ, ¬ M' ∣ n →
        ∃ h : ((ModularCurve.tateLaurent F').baseChange (Ω')).toAffine.Nonsingular
            (algebraMap (LaurentSeries F') (Ω') (ModularCurve.toricPoint F' 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries F') (Ω') (ModularCurve.toricPoint F' 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries F') (Ω') (ModularCurve.toricPoint F' 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries F') (Ω') (ModularCurve.toricPoint F' 1 (ζ ^ n)).2) h := by
    by_cases hM'2 : 2 ≤ M'
    · exact ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot F' M' hM'2 ζ hζ
        (Ω')
    · have hM'1 : M' = 1 := by omega
      refine ⟨0, fun n => ?_, fun n hn => ?_⟩
      · rw [hM'1]; simp
      · rw [hM'1] at hn; exact absurd (one_dvd n) hn

  have hgP : g ∈ AddSubgroup.zmultiples P := by
    refine mem_of_ordCompl_nsmul_mem (AddSubgroup.zmultiples P) g M' hM'0 ?_ ?_
    · rw [← hgord]; exact addOrderOf_nsmul_eq_zero g
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      set k := M'.factorization p with hk
      have hk0 : 0 < k := hpp.factorization_pos_of_dvd hM'0 (Nat.dvd_of_mem_primeFactors hp)
      have hpk : p ^ k ∣ M' := Nat.ordProj_dvd M' p
      have hord : addOrderOf ((M' / p ^ k) • g) = p ^ k := by
        rw [← hgord] at hpk ⊢
        exact addOrderOf_nsmul_addOrderOf_sub (hgord ▸ hM'0) hpk

      rcases hng : (M' / p ^ k) • g with _ | ⟨X, Y, hXY⟩
      · exact zero_mem _
      · obtain ⟨a, ha, hX⟩ := hcut p hp (M' / p ^ k) X Y hXY hng (hng ▸ hord)
        rw [Finset.mem_filter, Finset.mem_Icc] at ha
        obtain ⟨⟨ha1, ha2⟩, hpa⟩ := ha

        set m := M' / p ^ k * a with hm
        have hmM' : ¬ M' ∣ m := by
          intro hdvd
          have hmpos : 0 < m := Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM'0) hpk)
            (pow_pos hpp.pos k)) ha1
          have hmlt : m < M' := by
            have h2 : a < p ^ k := lt_of_le_of_lt ha2 (Nat.div_lt_self (pow_pos hpp.pos k) one_lt_two)
            calc m = M' / p ^ k * a := rfl
              _ < M' / p ^ k * p ^ k := Nat.mul_lt_mul_of_pos_left h2
                  (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM'0) hpk) (pow_pos hpp.pos k))
              _ = M' := Nat.div_mul_cancel hpk
          exact absurd (Nat.le_of_dvd hmpos hdvd) (not_le.mpr hmlt)
        obtain ⟨hns, hmP⟩ := hP m hmM'
        have hXm : X = algebraMap (LaurentSeries F') (Ω') (ModularCurve.toricPoint F' 1 (ζ ^ m)).1 := by
          rw [hX, ← pow_mul, incl_toricPoint_fst incl halg]
        rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hXY) (h₂ := hns)).mp hXm with h | h
        · rw [h, ← hmP]; exact (AddSubgroup.zmultiples P).nsmul_mem (AddSubgroup.mem_zmultiples P) m
        · rw [h, ← hmP]; exact AddSubgroup.neg_mem _ ((AddSubgroup.zmultiples P).nsmul_mem (AddSubgroup.mem_zmultiples P) m)
  have hle : AddSubgroup.zmultiples ((M' / d) • g) ≤ AddSubgroup.zmultiples P :=
    AddSubgroup.zmultiples_le_of_mem ((AddSubgroup.zmultiples P).nsmul_mem hgP _)
  have hH' : IsAddCyclic (AddSubgroup.zmultiples ((M' / d) • g)) ∧
      Nat.card (AddSubgroup.zmultiples ((M' / d) • g)) = d :=
    ⟨inferInstance, by rw [Nat.card_zmultiples, addOrderOf_div_nsmul g M' d hgord hM'0 hd]⟩
  rw [ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples F' (Ω') M' ζ hζ
    P hP0 hP d hd _ hH' hle, halg]

end TateSide
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget"

def fracSubfield {B E : Type*} [CommRing B] [Field E] (ι : B →+* E) : Subfield E where
  carrier := {k : E | ∃ a b : B, ι b ≠ 0 ∧ k * ι b = ι a}
  mul_mem' := by
    rintro k₁ k₂ ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
    refine ⟨a₁ * a₂, b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
    rw [map_mul, map_mul, ← h₁, ← h₂]; ring
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro k₁ k₂ ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
    refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]; ring
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro k ⟨a, b, hb, h⟩
    exact ⟨-a, b, hb, by rw [map_neg, ← h, neg_mul]⟩
  inv_mem' := by
    rintro k ⟨a, b, hb, h⟩
    by_cases hk : k = 0
    · exact ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [hk, inv_zero, map_zero, zero_mul]⟩
    · refine ⟨b, a, ?_, ?_⟩
      · rw [← h]; exact mul_ne_zero hk hb
      · rw [← h, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

theorem mem_fracSubfield_iff {B E : Type*} [CommRing B] [Field E] (ι : B →+* E) (k : E) :
    k ∈ fracSubfield ι ↔ ∃ a b : B, ι b ≠ 0 ∧ k * ι b = ι a := Iff.rfl

theorem rel_symm {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] {x y : R.Raw T} (h : R.Rel x y) : R.Rel y x := by
  obtain ⟨C, rfl⟩ := h
  exact ⟨C⁻¹, by rw [← R.act_mul, inv_mul_cancel, R.act_one]⟩

theorem rel_of_mk_eq_mk {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] {x y : R.Raw T}
    (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) : ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x :=
  (Equivalence.eqvGen_iff ⟨ModularCurve.RigidWeierstrassData.Rel.refl R, rel_symm R,
    ModularCurve.RigidWeierstrassData.Rel.trans R⟩).mp (Quot.eqvGen_exact h)

theorem jOfUnit_eq_div {F : Type*} [Field F] (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) :
    W.jOfUnit hΔ = W.c₄ ^ 3 / W.Δ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  rw [WeierstrassCurve.jOfUnit_eq_j, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    div_eq_mul_inv, mul_comm]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand]
  exact congrArg _ (map_jqModC f)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem exists_eq_of_isRoot_map_prod_X_sub_C {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (φ : R →+* S)
    (T : Finset ℕ) (c : ℕ → R) (z : S) (hz : ((∏ a ∈ T, (X - Polynomial.C (c a))).map φ).IsRoot z) :
    ∃ a ∈ T, z = φ (c a) := by
  rw [Polynomial.map_prod, Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨a, ha, h0⟩ := hz
  refine ⟨a, ha, ?_⟩
  rwa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at h0

section Key

variable (A : Type) [CommRing A] (ℓ M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K]
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (N₀ : ℕ) [NeZero N₀]
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L N₀)

    (𝕂 : Type) [Field 𝕂] [CharZero 𝕂] [Algebra A 𝕂] (ι' : P₀.B₀ →ₐ[A] 𝕂) (val𝕂 : 𝕂 →ₐ[A] ↥K)
    (hcomp : val𝕂.comp ι' = P₀.classify x)
    (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hrx : (Quot.mk _ r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x)
    (hcurve : r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L N₀)
    (hvi : ∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' N₀ (ζ ^ a)).1)))
    (d : ℕ) [NeZero d] (hd : d ∣ M')
    (F' : Type) [Field F'] (f : L →+* F') (hf : Function.Injective f) (ζM : F') (hζM : IsPrimitiveRoot ζM M')
    (Ω' : Type) [Field Ω'] [CharZero Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] [Algebra (LaurentSeries F') Ω']
    (incl : LaurentSeries F' →+* Ω') (hincl : Function.Injective incl)
    (halg : ∀ y, algebraMap (LaurentSeries F') Ω' y = incl (ModularCurve.qExpand F' N₀ y))

local notation "RD" => rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯

set_option maxHeartbeats 1600000 in
include hx hcomp hrx hcurve hvi hd hf hζM hincl halg in

theorem key : ∃ J : 𝕂, ((val𝕂 J : ↥K) : LaurentSeries L) = ModularCurve.qExpand L N₀ (ModularCurve.jqNModC L d) := by
  let ι : P₀.B₀ →+* ↥K := (P₀.classify x).toRingHom
  have hιapp : ∀ b, ι b = P₀.classify x b := fun b => rfl
  have hvalι' : ∀ b, val𝕂 (ι' b) = ι b := fun b => by rw [hιapp, ← hcomp]; rfl

  obtain ⟨u, hu⟩ := Quot.exists_rep P₀.univ
  set x𝕂 : (RD).Raw 𝕂 := (RD).mapRing ι' u with hx𝕂
  set r' : (RD).Raw ↥K := (RD).mapRing (P₀.classify x) u with hr'def
  have hr' : (Quot.mk _ r' : (RD).toLevelModuliDatum.Pt ↥K) = x := by
    have := P₀.map_classify x
    rw [← hu] at this
    exact this
  have hx𝕂K : (RD).mapRing val𝕂 x𝕂 = r' := by
    rw [hx𝕂, ← (RD).mapRing_comp, hcomp]
  obtain ⟨C₁, hC₁⟩ := rel_of_mk_eq_mk (RD) (hrx.trans hr'.symm)
  have hcurve' : r'.curve = C₁ • r.curve := by
    change (RD).curve r' = C₁ • (RD).curve r
    rw [hC₁]; exact (RD).curve_act C₁ r
  have hlevel' : ∀ p : ↥M'.primeFactors, r'.level.1 p =
      ModularCurve.kernelVariableChangeDeg C₁ (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
        (r.level.1 p) := by
    intro p; rw [hC₁]; rfl
  have hr'curve : r'.curve = u.curve.map ι := rfl
  have hr'level : ∀ p : ↥M'.primeFactors, r'.level.1 p = (u.level.1 p).map ι := fun p => rfl
  have hx𝕂curve : x𝕂.curve = u.curve.map ι'.toRingHom := rfl
  have hx𝕂level : ∀ p : ↥M'.primeFactors, x𝕂.level.1 p = (u.level.1 p).map ι'.toRingHom := fun p => rfl
  have hval𝕂ι' : val𝕂.toRingHom.comp ι'.toRingHom = ι := RingHom.ext fun b => hvalι' b

  have hjval : ((val𝕂 (x𝕂.curve.c₄ ^ 3 / x𝕂.curve.Δ) : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L N₀ := by
    rw [← hx, ← hr']
    change _ = (((r'.curve.jOfUnit r'.isUnit_Δ) : ↥K) : LaurentSeries L)
    rw [jOfUnit_eq_div, hr'curve, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, hx𝕂curve,
      WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow, ← hval𝕂ι']
    rfl
  have hjt : Transcendental ℚ (x𝕂.curve.c₄ ^ 3 / x𝕂.curve.Δ) := by
    have h1 : Transcendental ℚ (ModularCurve.jqNModC L N₀) :=
      Transcendental.of_ringHom_of_comp_eq (algebraMap ℚ L) (RingHom.id (LaurentSeries L))
        (ModularCurve.transcendental_jqNModC L N₀) (algebraMap ℚ L).injective (RingHom.ext_rat _ _)
    rw [← hjval] at h1
    exact Transcendental.of_ringHom_of_comp_eq (RingHom.id ℚ)
      ((algebraMap ↥K (LaurentSeries L)).comp val𝕂.toRingHom) h1 (RingHom.id ℚ).injective
      (RingHom.ext_rat _ _)

  let Ω : Type := AlgebraicClosure 𝕂
  haveI : DecidableEq Ω := Classical.decEq Ω
  let fΩ : 𝕂 →ₐ[A] Ω := IsScalarTower.toAlgHom A 𝕂 Ω
  set xΩ : (RD).Raw Ω := (RD).mapRing fΩ x𝕂 with hxΩ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap 𝕂 Ω).injective
  have hM'Ω : ((M' : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M')
  obtain ⟨g, hg⟩ := WeierstrassCurve.DrinfeldGlobal.exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataPow
    A ℓ M' q hℓ hM 𝒢 𝒯 Ω hM'Ω xΩ
  obtain ⟨J, hJ⟩ := WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow
    A ℓ M' q hℓ hM 𝒢 𝒯 𝕂 x𝕂 hjt Ω d hd
  have hJg := hJ g hg
  have hgcut : IsCutOut (x𝕂.curve.baseChange Ω) M' (fun p => (x𝕂.level.1 p).map (algebraMap 𝕂 Ω)) g := hg

  let cf : LaurentSeries L →+* LaurentSeries F' := ModularCurve.coeffMap f
  have hcf : Function.Injective cf := coeffMap_injective f hf
  let v : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L)
  have hv : ∀ k : ↥K, v k = (k : LaurentSeries L) := fun k => rfl
  let θ : ↥K →+* Ω' := incl.comp (cf.comp v)
  letI algΩ' : Algebra 𝕂 Ω' := (θ.comp val𝕂.toRingHom).toAlgebra
  have halgΩ' : algebraMap 𝕂 Ω' = θ.comp val𝕂.toRingHom := rfl
  have hθι : θ.comp ι = (algebraMap 𝕂 Ω').comp ι'.toRingHom := RingHom.ext fun b => by
    change θ (ι b) = θ (val𝕂.toRingHom (ι'.toRingHom b))
    rw [← hval𝕂ι']; rfl

  haveI : Module.IsTorsionFree 𝕂 Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap 𝕂 Ω).injective
  haveI : Module.IsTorsionFree 𝕂 Ω' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap 𝕂 Ω').injective
  let e : Ω →ₐ[𝕂] Ω' := IsAlgClosed.lift
  have hspec := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed x𝕂.curve (A := Ω) (B := Ω') e
    (AddSubgroup.zmultiples ((M' / d) • g)) d
  set g' : (x𝕂.curve.baseChange Ω').toAffine.Point := WeierstrassCurve.Affine.Point.map e g with hg'
  have hJ' : algebraMap 𝕂 Ω' J =
      (x𝕂.curve.baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g')) d := by
    rw [hg', ← map_nsmul, ← AddMonoidHom.map_zmultiples]
    refine Eq.trans ?_ hspec.symm
    have := congrArg e hJg
    rw [AlgHom.commutes] at this
    exact this
  have hcut' : IsCutOut (x𝕂.curve.baseChange Ω') M' (fun p => (x𝕂.level.1 p).map (algebraMap 𝕂 Ω')) g' := by
    refine IsCutOut.map (WeierstrassCurve.Affine.Point.map e) (WeierstrassCurve.Affine.Point.map_injective e) e
      (fun x y hxy => ⟨e y, _, WeierstrassCurve.Affine.Point.map_some e hxy⟩) _ _ (fun p z hz => ?_) hgcut
    have hcomp' : (algebraMap 𝕂 Ω') = (e : Ω →+* Ω').comp (algebraMap 𝕂 Ω) := (e.comp_algebraMap).symm
    change ((x𝕂.level.1 p).map (algebraMap 𝕂 Ω')).IsRoot ((e : Ω →+* Ω') z)
    rw [hcomp', ← Polynomial.map_map]
    exact hz.map

  have hcfq : (cf.comp (ModularCurve.qExpand L N₀)) = (ModularCurve.qExpand F' N₀).comp cf :=
    RingHom.ext fun y => coeffMap_qExpand f N₀ y
  have hTate : (ModularCurve.tateBase L N₀).map (incl.comp cf) = (ModularCurve.tateLaurent F').baseChange Ω' := by
    rw [ModularCurve.tateBase, WeierstrassCurve.map_map, RingHom.comp_assoc, hcfq, ← RingHom.comp_assoc,
      ← WeierstrassCurve.map_map, ModularCurve.map_coeffMap_tateLaurent, WeierstrassCurve.baseChange]
    congr 1
    exact RingHom.ext fun y => (halg y).symm
  set C₃ : WeierstrassCurve.VariableChange Ω' := C₁.map θ * C.map (incl.comp cf) with hC₃
  have heq : x𝕂.curve.baseChange Ω' = C₃ • (ModularCurve.tateLaurent F').baseChange Ω' := by
    calc x𝕂.curve.baseChange Ω' = r'.curve.map θ := by
            rw [WeierstrassCurve.baseChange, hx𝕂curve, WeierstrassCurve.map_map, ← hθι, hr'curve,
              WeierstrassCurve.map_map]
      _ = C₁.map θ • (r.curve.map v).map (incl.comp cf) := by
            rw [hcurve', ← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map]; rfl
      _ = C₃ • (ModularCurve.tateLaurent F').baseChange Ω' := by
            rw [hcurve, ← WeierstrassCurve.map_variableChange, hTate, hC₃, mul_smul]

  let hT : ↥M'.primeFactors → (LaurentSeries F')[X] := fun p =>
    ∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
      (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' N₀ ((ζM ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)
  have hζp : ∀ p : ↥M'.primeFactors,
      IsPrimitiveRoot (ζM ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ((p : ℕ) ^ M'.factorization (p : ℕ)) := by
    intro p
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' p
    exact hζM.pow (Nat.pos_of_ne_zero (NeZero.ne M')) (Nat.div_mul_cancel hpk).symm
  have hΦ : ∀ p : ↥M'.primeFactors, (x𝕂.level.1 p).map (algebraMap 𝕂 Ω') =
      ModularCurve.kernelVariableChangeDeg C₃ (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
        ((hT p).map incl) := by
    intro p
    have h1 : (x𝕂.level.1 p).map (algebraMap 𝕂 Ω') = (r'.level.1 p).map θ := by
      rw [hx𝕂level, Polynomial.map_map, ← hθι, hr'level, Polynomial.map_map]
    have h2 : (r.level.1 p).map θ = (((r.level.1 p).map v).map cf).map incl := by
      rw [Polynomial.map_map, Polynomial.map_map]; rfl
    rw [h1, hlevel', ModularCurve.kernelVariableChangeDeg_map, h2, hvi p F' f _ (hζp p),
      ModularCurve.kernelVariableChangeDeg_map, ← ModularCurve.kernelVariableChangeDeg_mul, hC₃,
      WeierstrassCurve.VariableChange.map_map]

  set g'' : (C₃ • (ModularCurve.tateLaurent F').baseChange Ω').toAffine.Point := ptCongr heq g' with hg''
  have hcut'' : IsCutOut (C₃ • (ModularCurve.tateLaurent F').baseChange Ω') M'
      (fun p => ModularCurve.kernelVariableChangeDeg C₃ (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
        ((hT p).map incl)) g'' := by
    refine IsCutOut.map (ptCongr heq).toAddMonoidHom (ptCongr heq).injective id
      (fun x y hxy => ⟨y, heq ▸ hxy, ptCongr_some heq x y hxy⟩) _ _ (fun p z hz => ?_) hcut'
    change (ModularCurve.kernelVariableChangeDeg C₃ _ ((hT p).map incl)).IsRoot z
    rw [← hΦ p]; exact hz
  set gT : ((ModularCurve.tateLaurent F').baseChange Ω').toAffine.Point :=
    vcAddEquiv C₃ ((ModularCurve.tateLaurent F').baseChange Ω') g'' with hgT
  have hcutT : IsCutOut ((ModularCurve.tateLaurent F').baseChange Ω') M' (fun p => (hT p).map incl) gT := by
    refine IsCutOut.map (vcAddEquiv C₃ ((ModularCurve.tateLaurent F').baseChange Ω')).toAddMonoidHom
      (vcAddEquiv C₃ _).injective (WeierstrassCurve.Affine.vcX C₃)
      (fun x y hxy => ⟨_, _, vcAddEquiv_some C₃ _ x y hxy⟩) _ _ (fun p z hz => ?_) hcut''
    exact isRoot_of_isRoot_kernelVariableChangeDeg C₃ _ _ z hz

  have htate : ((ModularCurve.tateLaurent F').baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • gT)) d =
      incl (ModularCurve.qExpand F' N₀ (ModularCurve.jqNModC F' d)) := by
    refine cyclicQuotientJ_zmultiples_eq_of_toric incl halg M' ζM hζM gT hcutT.1 ?_ d hd
    intro p hp n X Y hXY hn hord
    have hroot := hcutT.2 ⟨p, hp⟩ n X Y hXY hn hord
    exact exists_eq_of_isRoot_map_prod_X_sub_C incl _ _ X hroot

  have h1 : (x𝕂.curve.baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g')) d =
      (C₃ • (ModularCurve.tateLaurent F').baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g'')) d := by
    rw [← cyclicQuotientJ_map_ptCongr heq, AddMonoidHom.map_zmultiples, map_nsmul, hg'']
    rfl
  have hd0 : ((d : ℕ) : Ω') ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h2 : (C₃ • (ModularCurve.tateLaurent F').baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • g'')) d =
      ((ModularCurve.tateLaurent F').baseChange Ω').cyclicQuotientJ (AddSubgroup.zmultiples ((M' / d) • gT)) d := by
    refine WeierstrassCurve.cyclicQuotientJ_variableChange_eq C₃ _ _ _ (fun P => ?_) d hd0
    have := mem_zmultiples_iff_vcFun_mem C₃ _ ((M' / d) • g'') P
    rw [map_nsmul] at this
    rw [hgT]; exact this

  have hJread : incl (cf (((val𝕂 J : ↥K)) : LaurentSeries L)) = incl (cf (ModularCurve.qExpand L N₀ (ModularCurve.jqNModC L d))) := by
    have hl : algebraMap 𝕂 Ω' J = incl (cf ((val𝕂 J : ↥K) : LaurentSeries L)) := rfl
    rw [← hl, hJ', h1, h2, htate, coeffMap_qExpand, coeffMap_jqNModC]
  exact ⟨J, hcf (hincl hJread)⟩

end Key
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget"

section CoeffEmb

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (d : ℕ) [NeZero d] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ d x) = qExpand L d (coeffEmb L x) := by
  ext k
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd d _ hk, qExpand_coeff_of_not_dvd d _ hk, map_zero]

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  have h := Subsingleton.elim ((coeffEmb L).comp (algebraMap ℚ (LaurentSeries ℚ)))
    ((algebraMap L (LaurentSeries L)).comp (algebraMap ℚ L))
  exact congrArg (fun f : ℚ →+* LaurentSeries L => f r) h

end CoeffEmb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget"

end ModularCurve.Gamma0PowLayerAssembly
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve.Gamma0PowLayerAssembly.TatePowTarget P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve"

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve~coeffMap_qExpand~coeffEmb_jq~coeffEmb_qExpand~coeffMap_injective~coeffMap_jqNModC P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel"
open scoped MatrixGroups

open ModularCurve.Gamma0PowLayerAssembly in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))

    (hμ : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x ∧

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy)) :
    ∀ g : LaurentSeries L,
      g ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) →
        ∀ k : ↥K, ((k : ↥K) : LaurentSeries L) = ModularCurve.qExpand L (q * ℓ) g →
          ∃ a b : P₀.B₀, P₀.classify x b ≠ 0 ∧ k * P₀.classify x b = P₀.classify x a := by

  haveI hN0 : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨C, r, hrx, _htw, hcurve, hvi, _hiii, _hiv⟩ := hμ
  set ι : P₀.B₀ →+* ↥K := (P₀.classify x).toRingHom with hι
  have hιapp : ∀ b, ι b = P₀.classify x b := fun b => rfl

  set SK : Subfield ↥K := fracSubfield ι with hSK
  set S : Subfield (LaurentSeries L) := (SK.map (K.val).toRingHom).comap (qExpand L (q * ℓ)) with hS

  have hgoodL : ∀ c : L, algebraMap L ↥K c ∈ SK := by
    intro c
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) (S := L) c
    rw [hSK, mem_fracSubfield_iff]
    refine ⟨algebraMap A P₀.B₀ a, algebraMap A P₀.B₀ s, ?_, ?_⟩
    · rw [hιapp, AlgHom.commutes, IsScalarTower.algebraMap_apply A L ↥K]
      exact (map_ne_zero_iff _ (algebraMap L ↥K).injective).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.ne_zero s.2))
    · rw [hιapp, hιapp, AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply A L ↥K,
        IsScalarTower.algebraMap_apply A L ↥K, ← map_mul, hs]
  have hconst : ∀ c : L, algebraMap L (LaurentSeries L) c ∈ S := by
    intro c
    rw [hS, Subfield.mem_comap, Subfield.mem_map]
    refine ⟨algebraMap L ↥K c, hgoodL c, ?_⟩
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    show K.val (algebraMap L ↥K c) = _
    exact (K.val.commutes c).trans (algebraMap_laurentSeries_eq_single L c)

  have hSKmem : ∀ b : P₀.B₀, ι b ∈ SK := fun b =>
    ⟨b, 1, by rw [hιapp, map_one]; exact one_ne_zero, by rw [hιapp (1 : P₀.B₀), map_one, mul_one]⟩
  let ιSK : P₀.B₀ →+* ↥SK := ι.codRestrict SK hSKmem
  letI alg𝕂 : Algebra A ↥SK := (ιSK.comp (algebraMap A P₀.B₀)).toAlgebra
  have halg𝕂 : ∀ a : A, ((algebraMap A ↥SK a : ↥SK) : ↥K) = algebraMap A ↥K a := fun a => by
    change ι (algebraMap A P₀.B₀ a) = algebraMap A ↥K a
    rw [hιapp, AlgHom.commutes]
  let ι' : P₀.B₀ →ₐ[A] ↥SK :=
    { toRingHom := ιSK
      commutes' := fun a => rfl }
  let val𝕂 : ↥SK →ₐ[A] ↥K :=
    { toFun := fun k => (k : ↥K)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun a => halg𝕂 a }
  have hval𝕂 : ∀ k : ↥SK, val𝕂 k = (k : ↥K) := fun k => rfl
  have hcomp : val𝕂.comp ι' = P₀.classify x := AlgHom.ext fun b => rfl

  let F' : Type := CyclotomicField M' L
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap L F').injective
  have hζM : IsPrimitiveRoot (IsCyclotomicExtension.zeta M' L F') M' := IsCyclotomicExtension.zeta_spec M' L F'

  have hgen : ∀ (d : ℕ) [NeZero d], d ∣ M' → coeffEmb L (qExpand ℚ d jq) ∈ S := by
    intro d _ hdM
    rw [hS, Subfield.mem_comap, Subfield.mem_map, coeffEmb_qExpand, coeffEmb_jq]
    obtain ⟨J, hJ⟩ := key A ℓ M' q hℓ hM 𝒢 𝒯 L K P₀ x (q * ℓ) hx ↥SK ι' val𝕂 hcomp C r hrx hcurve hvi d hdM
      F' (algebraMap L F') (algebraMap L F').injective (IsCyclotomicExtension.zeta M' L F') hζM
      (TatePowTarget F' (q * ℓ)) (TatePowTarget.incl F' (q * ℓ)) (TatePowTarget.incl_injective F' (q * ℓ))
      (fun y => rfl)
    exact ⟨(J : ↥K), J.2, hJ⟩

  have hS' : ∀ g, g ∈ ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) → g ∈ S := by
    intro g hg
    rw [ModularCurve.mem_laurentBaseChange_iff] at hg
    refine Subfield.closure_le.mpr ?_ hg
    rintro y (⟨c, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact hconst c
    · rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull M'] at hz
      let T : IntermediateField ℚ (LaurentSeries ℚ) :=
        (S.comap (coeffEmb L)).toIntermediateField (fun r => by
          rw [Subfield.mem_comap, coeffEmb_algebraMap]; exact hconst _)
      have hle : modularFunctionFieldFull M' ≤ T := by
        rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
        rintro w ⟨d, hd0, hdM, rfl⟩
        haveI := hd0
        show qExpand ℚ d jq ∈ S.comap (coeffEmb L)
        rw [Subfield.mem_comap]
        exact hgen d hdM
      have hzT : z ∈ T := hle hz
      exact (Subfield.mem_comap.mp hzT)

  intro g hg k hk
  have hgS := hS' g hg
  rw [hS, Subfield.mem_comap, Subfield.mem_map] at hgS
  obtain ⟨k', hk'S, hk'eq⟩ := hgS
  have hkk : k' = k := Subtype.ext (hk'eq.trans hk.symm)
  subst hkk
  rw [hSK, mem_fracSubfield_iff] at hk'S
  obtain ⟨a, b, hb, hab⟩ := hk'S
  exact ⟨a, b, hb, hab⟩

end S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_classify_eq_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0Pow_tatePoint (solution)
