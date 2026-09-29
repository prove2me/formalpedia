-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8c77c679-bee6-5662-9f43-57a26b8f8a57

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
import Theorems.Thm_ModularCurve_SSHeckeV2_liftFun_spec
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
import Theorems.Thm_AlgebraicCurve_weilOfKaehler_omegaSpace_le_canonical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

namespace ThetaE4

section Local
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_sub_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem v hv hf (neg_mem hg), evalAt_neg_of_mem v hv hg, ← sub_eq_add_neg]

theorem evalAt_smul_of_mem (v : Place K F) (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  have hcf : c • f ∈ v.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' c) hf
  apply (algebraMap K v.ResidueField).injective
  rw [v.algebraMap_evalAt hv hcf, map_mul, v.algebraMap_evalAt hv hf]
  have : (⟨c • f, hcf⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring c * ⟨f, hf⟩ := by
    apply Subtype.ext
    simp [Algebra.smul_def, Place.coe_algebraMap]
  rw [this, map_mul]
  congr 1

def HasFloor (v : Place K F) (a : ℤ) (f : F) : Prop := f = 0 ∨ -a ≤ v.ord f

theorem hasFloor_iff_adicValuation_le (v : Place K F) (a : ℤ) (f : F) :
    HasFloor v a f ↔ v.adicValuation f ≤ WithZero.exp a := by
  rw [HasFloor, v.adicValuation_le_exp_iff]

theorem HasFloor.zero (v : Place K F) (a : ℤ) : HasFloor v a (0 : F) := Or.inl rfl

theorem HasFloor.add {v : Place K F} {a : ℤ} {f g : F} (hf : HasFloor v a f) (hg : HasFloor v a g) :
    HasFloor v a (f + g) := by
  rw [hasFloor_iff_adicValuation_le] at *
  exact (Valuation.map_add _ _ _).trans (max_le hf hg)

theorem HasFloor.neg {v : Place K F} {a : ℤ} {f : F} (hf : HasFloor v a f) : HasFloor v a (-f) := by
  rw [hasFloor_iff_adicValuation_le] at *
  rwa [Valuation.map_neg]

theorem HasFloor.sub {v : Place K F} {a : ℤ} {f g : F} (hf : HasFloor v a f) (hg : HasFloor v a g) :
    HasFloor v a (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem HasFloor.smul {v : Place K F} {a : ℤ} (c : K) {f : F} (hf : HasFloor v a f) : HasFloor v a (c • f) := by
  rw [hasFloor_iff_adicValuation_le] at *
  rw [Algebra.smul_def, map_mul]
  exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans hf

theorem HasFloor.mono {v : Place K F} {a b : ℤ} {f : F} (hf : HasFloor v a f) (hab : a ≤ b) : HasFloor v b f := by
  rcases hf with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem HasFloor.zpow_mul_mem {v : Place K F} {a : ℤ} {f : F} (hf : HasFloor v a f) {π : F} (hπ : v.ord π = 1) :
    π ^ a * f ∈ v.toValuationSubring := by
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  have h : -a ≤ v.ord f := hf.resolve_left hf0
  rw [Place.mem_iff_ord_nonneg _ (mul_ne_zero (zpow_ne_zero a hπ0) hf0),
    Place.ord_mul _ (zpow_ne_zero a hπ0) hf0, Place.ord_zpow, hπ, mul_one]
  omega

theorem HasFloor.of_evalAt_eq_zero {v : Place K F} (hv : v.IsRational) {a : ℤ} {f : F} (hf : HasFloor v a f)
    {π : F} (hπ : v.ord π = 1) (h0 : v.evalAt (π ^ a * f) = 0) :
    HasFloor v (a - 1) f := by
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl rfl
  have hne : π ^ a * f ≠ 0 := mul_ne_zero (zpow_ne_zero a hπ0) hf0
  have h1 : 1 ≤ v.ord (π ^ a * f) := (v.evalAt_eq_zero_iff_one_le_ord hv hne (hf.zpow_mul_mem hπ)).mp h0
  rw [Place.ord_mul _ (zpow_ne_zero a hπ0) hf0, Place.ord_zpow, hπ, mul_one] at h1
  exact Or.inr (by omega)

theorem evalAt_eq_zero_of_hasFloor_sub_one {v : Place K F} (hv : v.IsRational) {a : ℤ} {f : F}
    (hf : HasFloor v (a - 1) f) {π : F} (hπ : v.ord π = 1) :
    v.evalAt (π ^ a * f) = 0 := by
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero, Place.evalAt, dif_pos (zero_mem _)]
    have : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
    rw [this, map_zero, ← map_zero (algebraMap K v.ResidueField), Place.residueInv_algebraMap]
  have hne : π ^ a * f ≠ 0 := mul_ne_zero (zpow_ne_zero a hπ0) hf0
  refine (v.evalAt_eq_zero_iff_one_le_ord hv hne ((hf.mono (by omega)).zpow_mul_mem hπ)).mpr ?_
  rw [Place.ord_mul _ (zpow_ne_zero a hπ0) hf0, Place.ord_zpow, hπ, mul_one]
  have := hf.resolve_left hf0
  omega

end Local

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in

noncomputable def localAdeleFun (T : Finset (Place K F)) (g : F) : Place K F → F :=
  fun w => if w ∈ T then g else 0

theorem localAdeleFun_of_mem {T : Finset (Place K F)} (g : F) {w : Place K F} (hw : w ∈ T) :
    localAdeleFun T g w = g := by
  unfold localAdeleFun; exact if_pos hw

theorem localAdeleFun_of_not_mem {T : Finset (Place K F)} (g : F) {w : Place K F} (hw : w ∉ T) :
    localAdeleFun T g w = 0 := by
  unfold localAdeleFun; exact if_neg hw

theorem localAdeleFun_mem_adeleBdd {T : Finset (Place K F)} {g : F} {D : Divisor K F}
    (hg : ∀ x ∈ T, x.adicValuation g ≤ WithZero.exp (D x)) : localAdeleFun T g ∈ adeleBdd D := by
  intro w
  by_cases hw : w ∈ T
  · rw [localAdeleFun_of_mem g hw]; exact hg w hw
  · rw [localAdeleFun_of_not_mem g hw, Valuation.map_zero]; exact zero_le'

noncomputable def localAdele (D : Divisor K F) (T : Finset (Place K F)) (g : F)
    (hg : ∀ x ∈ T, x.adicValuation g ≤ WithZero.exp (D x)) : ↥(adeleSpace K F) :=
  ⟨localAdeleFun T g, adeleBdd_le_adeleSpace (localAdeleFun_mem_adeleBdd hg)⟩

@[scoped simp] theorem coe_localAdele (D : Divisor K F) (T : Finset (Place K F)) (g : F)
    (hg : ∀ x ∈ T, x.adicValuation g ≤ WithZero.exp (D x)) :
    ((localAdele D T g hg : ↥(adeleSpace K F)) : Place K F → F) = localAdeleFun T g := rfl

theorem omega_eval_eq_add {D : Divisor K F} (μ : ↥(omegaSpace (K := K) (F := F) D)) (s a b : ↥(adeleSpace K F))
    (h : ((s : Place K F → F) - a - b) ∈ adeleBdd D) :
    (μ : Module.Dual K ↥(adeleSpace K F)) s = (μ : Module.Dual K ↥(adeleSpace K F)) a + (μ : Module.Dual K ↥(adeleSpace K F)) b := by
  have h0 : (μ : Module.Dual K ↥(adeleSpace K F)) (s - a - b) = 0 :=
    omegaSpace_vanishBdd μ.2 (by simpa only [Submodule.coe_sub] using h)
  rw [map_sub, map_sub] at h0
  linear_combination h0

theorem omega_eval_eq_smul {D : Divisor K F} (μ : ↥(omegaSpace (K := K) (F := F) D)) (s a : ↥(adeleSpace K F)) (c : K)
    (h : ((s : Place K F → F) - c • (a : Place K F → F)) ∈ adeleBdd D) :
    (μ : Module.Dual K ↥(adeleSpace K F)) s = c * (μ : Module.Dual K ↥(adeleSpace K F)) a := by
  have h0 : (μ : Module.Dual K ↥(adeleSpace K F)) (s - c • a) = 0 :=
    omegaSpace_vanishBdd μ.2 (by simpa only [Submodule.coe_sub, Submodule.coe_smul] using h)
  rw [map_sub, map_smul, smul_eq_mul] at h0
  linear_combination h0

theorem omega_eval_eq_zero_of_sub_diagonal [HasPrincipalDivisors K F] {D : Divisor K F}
    (μ : ↥(omegaSpace (K := K) (F := F) D)) (s : ↥(adeleSpace K F)) (G : F)
    (h : ((s : Place K F → F) - diagonalHom K F G) ∈ adeleBdd D) :
    (μ : Module.Dual K ↥(adeleSpace K F)) s = 0 := by
  have h1 : (μ : Module.Dual K ↥(adeleSpace K F)) ⟨diagonalHom K F G, diagonal_mem_adeleSpace G⟩ = 0 :=
    omegaSpace_vanishGlobal μ.2 (diagonal_mem_globalSub G)
  have h2 : (μ : Module.Dual K ↥(adeleSpace K F)) (s - ⟨diagonalHom K F G, diagonal_mem_adeleSpace G⟩) = 0 :=
    omegaSpace_vanishBdd μ.2 (by simpa only [Submodule.coe_sub] using h)
  rw [map_sub, h1, sub_zero] at h2
  exact h2

noncomputable def thetaOf {V : Type*} [AddCommGroup V] [Module K V] (D : Divisor K F) (R : V → ↥(adeleSpace K F))
    (hadd : ∀ v w, ((R (v + w) : Place K F → F) - R v - R w) ∈ adeleBdd D)
    (hsmul : ∀ (c : K) v, ((R (c • v) : Place K F → F) - c • (R v : Place K F → F)) ∈ adeleBdd D) :
    V →ₗ[K] Module.Dual K ↥(omegaSpace (K := K) (F := F) D) where
  toFun v := (Module.Dual.eval K ↥(adeleSpace K F) (R v)) ∘ₗ (omegaSpace (K := K) (F := F) D).subtype
  map_add' v w := by
    ext μ
    exact omega_eval_eq_add μ (R (v + w)) (R v) (R w) (hadd v w)
  map_smul' c v := by
    ext μ
    exact omega_eval_eq_smul μ (R (c • v)) (R v) c (hsmul c v)

theorem thetaOf_apply {V : Type*} [AddCommGroup V] [Module K V] (D : Divisor K F) (R : V → ↥(adeleSpace K F))
    (hadd : ∀ v w, ((R (v + w) : Place K F → F) - R v - R w) ∈ adeleBdd D)
    (hsmul : ∀ (c : K) v, ((R (c • v) : Place K F → F) - c • (R v : Place K F → F)) ∈ adeleBdd D)
    (v : V) (μ : ↥(omegaSpace (K := K) (F := F) D)) :
    thetaOf D R hadd hsmul v μ = (μ : Module.Dual K ↥(adeleSpace K F)) (R v) := rfl

end Generic

section Modular

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)

theorem ord_unif (x : Place K ↥(modularFunctionFieldC K N)) : x.ord (ModularCurve.unif N K x) = 1 :=
  Classical.epsilon_spec (p := fun π : ↥(modularFunctionFieldC K N) => x.ord π = 1) x.exists_ord_eq_one

include hN in
theorem not_dvd : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)

def idx (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K) (hdvd : (placeWidth N x : ℤ) ∣ (m : ℤ)) :
    ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)) :=
  ⟨x, hx, by omega, ⟨m, rfl⟩, by simpa using hdvd, hp5⟩

include hN in

theorem weightDivisor_eq_poleOrder (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))) :
    ModularCurve.weightDivisor K N m x.1 = ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x := by
  have haff : IsAffineGeomPlace K N x.1 := x.2.1.2.1
  rw [ModularCurve.weightDivisor_apply K N m (ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m) x.1,
    ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N (not_dvd p K N hN) K m x.1 haff, ModularCurve.poleOrder]
  congr 1
  congr 1
  omega

include hN in
theorem resFnFun_apply (G : ↥(modularFunctionFieldC K N)) (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))) :
    ModularCurve.resFnFun p N K hp5 m G x
      = x.1.evalAt (ModularCurve.unif N K x.1 ^ (ModularCurve.weightDivisor K N m x.1) * G) := by
  rw [weightDivisor_eq_poleOrder p hp5 K N hN m]
  rfl

include hN in

theorem liftFun_floor (v : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ))) (z : Place K ↥(modularFunctionFieldC K N)) (hz : z ∈ ssPlaces p N K) :
    HasFloor z (ModularCurve.weightDivisor K N m z) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v) := by
  have h := (ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) v).1 z hz
  have e : (2 * (m : ℤ) / 2).toNat = m := by simp
  rw [e] at h
  exact Or.inr h

include hN in
theorem liftFun_lead (v : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ))) (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))) :
    x.1.evalAt (ModularCurve.unif N K x.1 ^ (ModularCurve.weightDivisor K N m x.1) * ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)
      = v x := by
  have h := (ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) v).2 x
  rw [weightDivisor_eq_poleOrder p hp5 K N hN m]
  exact h

theorem liftFun_val_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) :
    ∀ x ∈ T, x.adicValuation ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) ≤ WithZero.exp ((ModularCurve.weightDivisor K N m) x) := fun x hx =>
  (hasFloor_iff_adicValuation_le _ _ _).mp (liftFun_floor p hp5 K N hN m v x ((memT x).mp hx).1)

noncomputable def rAdele (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) : ↥(adeleSpace K ↥(modularFunctionFieldC K N)) :=
  localAdele (ModularCurve.weightDivisor K N m) T ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) (liftFun_val_le p hp5 K N hN m hm T memT v)

theorem rAdele_T (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) {w : Place K ↥(modularFunctionFieldC K N)} (hw : w ∈ T) :
    (rAdele p hp5 K N hN m hm T memT v : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N)) w = (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v := by
  show localAdeleFun T ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) w = _
  exact localAdeleFun_of_mem _ hw

theorem rAdele_nT (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) {w : Place K ↥(modularFunctionFieldC K N)} (hw : w ∉ T) :
    (rAdele p hp5 K N hN m hm T memT v : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N)) w = 0 := by
  show localAdeleFun T ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) w = _
  exact localAdeleFun_of_not_mem _ hw

theorem exists_idx (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) {w : Place K ↥(modularFunctionFieldC K N)} (hw : w ∈ T) : ∃ x : (ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ))), x.1 = w :=
  ⟨idx p hp5 K N m hm w ((memT w).mp hw).1 ((memT w).mp hw).2, rfl⟩

theorem idx_mem (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) (x : (ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))) : x.1 ∈ T := by
  obtain ⟨hss, -, -, hdvd, -⟩ := x.2
  exact (memT x.1).mpr ⟨hss, by simpa using hdvd⟩

theorem hasFloor_D' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) (x : (ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))) (f : ↥(modularFunctionFieldC K N)) (hf : HasFloor x.1 ((ModularCurve.weightDivisor K N m) x.1) f)
    (h0 : x.1.evalAt (ModularCurve.unif N K x.1 ^ ((ModularCurve.weightDivisor K N m) x.1) * f) = 0) : HasFloor x.1 (D' x.1) f := by
  rw [hD'T x.1 (idx_mem p hp5 K N hN m hm T memT x)]
  exact hf.of_evalAt_eq_zero x.2.1.1 (ord_unif K N x.1) h0

theorem rAdele_add_bdd (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) (v w : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) :
    ((rAdele p hp5 K N hN m hm T memT (v + w) : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N)) - rAdele p hp5 K N hN m hm T memT v - rAdele p hp5 K N hN m hm T memT w) ∈ adeleBdd D' := by
  intro z
  rw [Pi.sub_apply, Pi.sub_apply]
  by_cases hz : z ∈ T
  · obtain ⟨x, rfl⟩ := exists_idx p hp5 K N hN m hm T memT hz
    rw [rAdele_T p hp5 K N hN m hm T memT _ hz, rAdele_T p hp5 K N hN m hm T memT _ hz, rAdele_T p hp5 K N hN m hm T memT _ hz, ← hasFloor_iff_adicValuation_le]
    have hfl := fun u => liftFun_floor p hp5 K N hN m u x.1 x.2.1
    refine hasFloor_D' p hp5 K N hN m hm T memT D' hD'T hD'nT x _ (((hfl (v + w)).sub (hfl v)).sub (hfl w)) ?_
    have hπ := ord_unif K N x.1
    rw [mul_sub, mul_sub, evalAt_sub_of_mem x.1 x.2.1.1 (sub_mem ((hfl _).zpow_mul_mem hπ) ((hfl _).zpow_mul_mem hπ)) ((hfl _).zpow_mul_mem hπ),
      evalAt_sub_of_mem x.1 x.2.1.1 ((hfl _).zpow_mul_mem hπ) ((hfl _).zpow_mul_mem hπ),
      liftFun_lead p hp5 K N hN m, liftFun_lead p hp5 K N hN m, liftFun_lead p hp5 K N hN m]
    simp
  · rw [rAdele_nT p hp5 K N hN m hm T memT _ hz, rAdele_nT p hp5 K N hN m hm T memT _ hz, rAdele_nT p hp5 K N hN m hm T memT _ hz, sub_zero, sub_zero,
      Valuation.map_zero]
    exact zero_le'

theorem rAdele_smul_bdd (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) (c : K) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) :
    ((rAdele p hp5 K N hN m hm T memT (c • v) : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N)) - c • (rAdele p hp5 K N hN m hm T memT v : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N))) ∈ adeleBdd D' := by
  intro z
  rw [Pi.sub_apply, Pi.smul_apply]
  by_cases hz : z ∈ T
  · obtain ⟨x, rfl⟩ := exists_idx p hp5 K N hN m hm T memT hz
    rw [rAdele_T p hp5 K N hN m hm T memT _ hz, rAdele_T p hp5 K N hN m hm T memT _ hz, ← hasFloor_iff_adicValuation_le]
    have hfl := fun u => liftFun_floor p hp5 K N hN m u x.1 x.2.1
    refine hasFloor_D' p hp5 K N hN m hm T memT D' hD'T hD'nT x _ ((hfl (c • v)).sub ((hfl v).smul c)) ?_
    have hπ := ord_unif K N x.1
    rw [mul_sub, evalAt_sub_of_mem x.1 x.2.1.1 ((hfl _).zpow_mul_mem hπ) (((hfl v).smul c).zpow_mul_mem hπ),
      mul_smul_comm, evalAt_smul_of_mem x.1 x.2.1.1 c ((hfl _).zpow_mul_mem hπ),
      liftFun_lead p hp5 K N hN m, liftFun_lead p hp5 K N hN m]
    simp
  · rw [rAdele_nT p hp5 K N hN m hm T memT _ hz, rAdele_nT p hp5 K N hN m hm T memT _ hz, smul_zero, sub_zero, Valuation.map_zero]
    exact zero_le'

noncomputable def theta (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ))) →ₗ[K] Module.Dual K ↥(omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D') :=
  thetaOf (V := (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) D' (rAdele p hp5 K N hN m hm T memT)
    (rAdele_add_bdd p hp5 K N hN m hm T memT D' hD'T hD'nT) (rAdele_smul_bdd p hp5 K N hN m hm T memT D' hD'T hD'nT)

theorem theta_apply (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) (μ : ↥(omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) :
    theta p hp5 K N hN m hm T memT D' hD'T hD'nT v μ = (μ : Module.Dual K ↥(adeleSpace K ↥(modularFunctionFieldC K N))) (rAdele p hp5 K N hN m hm T memT v) := rfl

theorem exists_of_theta_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) (hv : theta p hp5 K N hN m hm T memT D' hD'T hD'nT v = 0) :
    ∃ G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m), ModularCurve.resFnFun p N K hp5 m G = v := by
  classical
  have hsubD : (ModularCurve.weightDivisor K N m) - ∑ x ∈ T, Finsupp.single x 1 = D' := by
    ext w
    rw [Finsupp.sub_apply, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases hw : w ∈ T
    · rw [if_pos hw, hD'T w hw]
    · rw [if_neg hw, hD'nT w hw, sub_zero]
  have horth : ∀ μ : Module.Dual K ↥(adeleSpace K ↥(modularFunctionFieldC K N)),
      μ ∈ omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) ((ModularCurve.weightDivisor K N m) - ∑ x ∈ T, Finsupp.single x 1) → μ (rAdele p hp5 K N hN m hm T memT v) = 0 := by
    intro μ hμ
    rw [hsubD] at hμ
    have h := DFunLike.congr_fun hv ⟨μ, hμ⟩
    rw [theta_apply, LinearMap.zero_apply] at h
    exact h
  obtain ⟨f, hfL, hf⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_forall_adicValuation_sub_le_of_forall_omegaSpace
      (ModularCurve.weightDivisor K N m) T (fun _ => (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) (liftFun_val_le p hp5 K N hN m hm T memT v) (rAdele p hp5 K N hN m hm T memT v)
      (fun w hw => rAdele_T p hp5 K N hN m hm T memT v hw) (fun w hw => rAdele_nT p hp5 K N hN m hm T memT v hw) horth
  refine ⟨f, hfL, ?_⟩
  funext x
  have hx : x.1 ∈ T := idx_mem p hp5 K N hN m hm T memT x
  have hfx : HasFloor x.1 ((ModularCurve.weightDivisor K N m) x.1 - 1) (f - (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) := (hasFloor_iff_adicValuation_le _ _ _).mpr (hf x.1 hx)
  have hπ := ord_unif K N x.1
  have hfl : HasFloor x.1 ((ModularCurve.weightDivisor K N m) x.1) ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) := liftFun_floor p hp5 K N hN m v x.1 x.2.1
  have hsplit : f = (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v + (f - (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) := by ring
  rw [resFnFun_apply p hp5 K N hN m, hsplit, mul_add,
    evalAt_add_of_mem x.1 x.2.1.1 (hfl.zpow_mul_mem hπ) ((hfx.mono (by omega)).zpow_mul_mem hπ),
    liftFun_lead p hp5 K N hN m, evalAt_eq_zero_of_hasFloor_sub_one x.2.1.1 hfx hπ, add_zero]

theorem theta_resFnFun_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w) [HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    (G : ↥(modularFunctionFieldC K N)) (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    theta p hp5 K N hN m hm T memT D' hD'T hD'nT (ModularCurve.resFnFun p N K hp5 m G) = 0 := by
  ext μ
  rw [theta_apply, LinearMap.zero_apply]
  refine omega_eval_eq_zero_of_sub_diagonal μ _ G ?_
  intro z
  rw [Pi.sub_apply, diagonalHom_apply]
  have hGz : HasFloor z ((ModularCurve.weightDivisor K N m) z) G := by
    rcases (AlgebraicCurve.mem_riemannRochSpace_iff.mp hG) z with h | h
    · exact Or.inl h
    · exact Or.inr h
  by_cases hz : z ∈ T
  · obtain ⟨x, rfl⟩ := exists_idx p hp5 K N hN m hm T memT hz
    rw [rAdele_T p hp5 K N hN m hm T memT _ hz, ← hasFloor_iff_adicValuation_le]
    have hfl := liftFun_floor p hp5 K N hN m (ModularCurve.resFnFun p N K hp5 m G) x.1 x.2.1
    refine hasFloor_D' p hp5 K N hN m hm T memT D' hD'T hD'nT x _ (hfl.sub hGz) ?_
    have hπ := ord_unif K N x.1
    rw [mul_sub, evalAt_sub_of_mem x.1 x.2.1.1 (hfl.zpow_mul_mem hπ) (hGz.zpow_mul_mem hπ),
      liftFun_lead p hp5 K N hN m, resFnFun_apply p hp5 K N hN m, sub_self]
  · rw [rAdele_nT p hp5 K N hN m hm T memT _ hz, zero_sub, Valuation.map_neg, ← hasFloor_iff_adicValuation_le, hD'nT z hz]
    exact hGz

theorem theta_weilOfKaehler (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (T : Finset (Place K ↥(modularFunctionFieldC K N))) (memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)))
    (D' : Divisor K ↥(modularFunctionFieldC K N)) (hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1) (hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w)
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    (SS : Finset (Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K) (hTSS : T ⊆ SS)
    (v : (ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)))) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
    (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D') :
    theta p hp5 K N hN m hm T memT D' hD'T hD'nT v ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
      = ∑ x ∈ SS, kaehlerResidueTerm ω (diagonalHom K ↥(modularFunctionFieldC K N) ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v)) x := by
  rw [theta_apply]
  change AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω (rAdele p hp5 K N hN m hm T memT v) = _
  rw [weilOfKaehler_apply]
  have hsupp : Function.support (kaehlerResidueTerm ω (rAdele p hp5 K N hN m hm T memT v : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N))) ⊆ (T : Set (Place K ↥(modularFunctionFieldC K N))) := by
    intro z hz
    by_contra hzT
    apply hz
    exact kaehlerResidueTerm_eq_zero_of_ord_nonneg (Or.inl (by rw [rAdele_nT p hp5 K N hN m hm T memT v hzT, zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hT : ∀ z ∈ T, kaehlerResidueTerm ω (rAdele p hp5 K N hN m hm T memT v : Place K ↥(modularFunctionFieldC K N) → ↥(modularFunctionFieldC K N)) z
      = kaehlerResidueTerm ω (diagonalHom K ↥(modularFunctionFieldC K N) ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v)) z := by
    intro z hz
    unfold kaehlerResidueTerm
    rw [rAdele_T p hp5 K N hN m hm T memT v hz, diagonalHom_apply]
  rw [Finset.sum_congr rfl hT]
  apply Finset.sum_subset hTSS
  intro z hzSS hzT
  have hle := AlgebraicCurve.weilOfKaehler_omegaSpace_le_canonical hω hmem
  have hz' : D' z ≤ z.ordDifferential ω := by
    have := hle z
    rwa [canonicalDivisorOf_apply hω z] at this
  rw [hD'nT z hzT] at hz'
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := z.differentialCoeff_ne_zero hω
    rw [z.ord_mul h0 hg]
    have hfl : -((ModularCurve.weightDivisor K N m) z) ≤ z.ord ((ModularCurve.liftFun p N K hp5 (2 * (m : ℤ))) v) := (liftFun_floor p hp5 K N hN m v z ((hSS z).mp hzSS)).resolve_left h0
    rw [Place.ordDifferential] at hz'
    omega

end Modular

end ThetaE4
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler.ThetaE4"

open ThetaE4 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (SS : Finset (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w) :
    ∃ Θ : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)) →ₗ[K]
        Module.Dual K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
      (∀ v, Θ v = 0 ↔ ∃ G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m),
          ModularCurve.resFnFun p N K hp5 m G = v) ∧
      (∀ v (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
          (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈
            AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
          Θ v ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
            = ∑ x ∈ SS, kaehlerResidueTerm ω
                (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) x) := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Place K ↥(modularFunctionFieldC K N)),
      T = SS.filter (fun w => (placeWidth N w : ℤ) ∣ (m : ℤ)) := ⟨_, rfl⟩
  have memT : ∀ w, w ∈ T ↔ w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ)) := by
    intro w; rw [hTdef, Finset.mem_filter, hSS]
  have hTSS : T ⊆ SS := by rw [hTdef]; exact Finset.filter_subset _ SS
  have hD'T : ∀ w, w ∈ T → D' w = (ModularCurve.weightDivisor K N m) w - 1 :=
    fun w hw => hD'1 w ((memT w).mp hw).1 ((memT w).mp hw).2
  have hD'nT : ∀ w, w ∉ T → D' w = (ModularCurve.weightDivisor K N m) w :=
    fun w hw => hD'0 w (fun h => hw ((memT w).mpr h))
  exact ⟨theta p hp5 K N hN m hm T memT D' hD'T hD'nT,
    fun v => ⟨exists_of_theta_eq_zero p hp5 K N hN m hm T memT D' hD'T hD'nT v,
      fun ⟨G, hG, hv⟩ => hv ▸ theta_resFnFun_eq_zero p hp5 K N hN m hm T memT D' hD'T hD'nT G hG⟩,
    fun v ω hω hmem => theta_weilOfKaehler p hp5 K N hN m hm T memT D' hD'T hD'nT SS hSS hTSS v ω hω hmem⟩

end S_ModularCurve_SSHeckeV2_exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_exists_theta_ker_iff_range_resFnFun_and_apply_weilOfKaehler (solution)
