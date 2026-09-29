-- Prove2me | solution 1 for ModularCurve.frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b78ff5f2-37cd-5067-9159-67e460554a82

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_isModuliPlaceOf_map_frobenius_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace FrobA

section Twist

def Twist (κ : Type) (q' : ℕ) (Ω : Type) : Type := Ω

variable {κ : Type} [Field κ] {q' : ℕ} [Fact q'.Prime] [CharP κ q'] [PerfectRing κ q']

scoped instance Twist.instField (Ω : Type) [Field Ω] : Field (Twist κ q' Ω) := ‹Field Ω›
p2m_reactivate "P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA.Twist"
scoped instance Twist.instDecidableEq (Ω : Type) [DecidableEq Ω] : DecidableEq (Twist κ q' Ω) := ‹DecidableEq Ω›
p2m_reactivate "P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA.Twist"
noncomputable scoped instance Twist.instAlgebra (Ω : Type) [Field Ω] [Algebra κ Ω] : Algebra κ (Twist κ q' Ω) :=
  ((algebraMap κ Ω).comp ((frobeniusEquiv κ q').symm : κ →+* κ)).toAlgebra

p2m_reactivate "P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA.Twist"
theorem Twist.algebraMap_apply (Ω : Type) [Field Ω] [Algebra κ Ω] (c : κ) :
    algebraMap κ (Twist κ q' Ω) c = (algebraMap κ Ω ((frobeniusEquiv κ q').symm c) : Ω) := rfl

end Twist
p2m_reactivate "P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA.Twist"

open ModularCurve

variable (κ : Type) [Field κ] [DecidableEq κ] (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [PerfectField κ] (N : ℕ) [NeZero N]

theorem coeffMap_mem_full (τ : κ →+* κ) {x : LaurentSeries κ} (hx : x ∈ modularFunctionFieldFullC κ N) :
    coeffMap τ x ∈ modularFunctionFieldFullC κ N := by
  change x ∈ Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ divisorExpansionsC κ N) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap]
        exact (modularFunctionFieldFullC κ N).algebraMap_mem _
      · obtain ⟨d, hd, hdN, rfl⟩ := hy
        rw [coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC]
        exact jqModCd_mem_full κ N hdN
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def coeffRingAutFull (τ : κ ≃+* κ) : ↥(modularFunctionFieldFullC κ N) ≃+* ↥(modularFunctionFieldFullC κ N) where
  toFun x := ⟨coeffMap (τ : κ →+* κ) (x : LaurentSeries κ), coeffMap_mem_full κ N (τ : κ →+* κ) x.2⟩
  invFun x := ⟨coeffMap (τ.symm : κ →+* κ) (x : LaurentSeries κ), coeffMap_mem_full κ N (τ.symm : κ →+* κ) x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (τ.symm : κ →+* κ) (coeffMap (τ : κ →+* κ) (x : LaurentSeries κ)) = (x : LaurentSeries κ)
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id κ) (RingHom.ext fun a => τ.symm_apply_apply a) _, coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (τ : κ →+* κ) (coeffMap (τ.symm : κ →+* κ) (x : LaurentSeries κ)) = (x : LaurentSeries κ)
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id κ) (RingHom.ext fun a => τ.apply_symm_apply a) _, coeffMap_id]
  map_mul' x y := Subtype.ext (map_mul (coeffMap (τ : κ →+* κ)) (x : LaurentSeries κ) (y : LaurentSeries κ))
  map_add' x y := Subtype.ext (map_add (coeffMap (τ : κ →+* κ)) (x : LaurentSeries κ) (y : LaurentSeries κ))

noncomputable def coeffSemilinearAutFull (τ : κ ≃+* κ) : AlgebraicCurve.SemilinearAut κ ↥(modularFunctionFieldFullC κ N) :=
  ⟨(coeffRingAutFull κ N τ, τ), fun a => Subtype.ext (coeffMap_algebraMap (τ : κ →+* κ) a)⟩

theorem exists_fullArithFrob :
    ∃ σ : AlgebraicCurve.SemilinearAut κ ↥(modularFunctionFieldFullC κ N),
      (∀ x : ↥(modularFunctionFieldFullC κ N),
        ((σ • x : ↥(modularFunctionFieldFullC κ N)) : LaurentSeries κ) = coeffMap (frobenius κ q') (x : LaurentSeries κ)) ∧
      (∀ a : κ, AlgebraicCurve.SemilinearAut.baseAut σ a = a ^ q') ∧
      (∀ x : ↥(modularFunctionFieldC κ N),
        IntermediateField.inclusion (modularFunctionFieldC_le_full κ N) (arithFrobC q' κ N • x) =
          σ • IntermediateField.inclusion (modularFunctionFieldC_le_full κ N) x) := by
  refine ⟨coeffSemilinearAutFull κ N (frobeniusEquiv κ q'), fun x => rfl, fun a => rfl, fun x => Subtype.ext rfl⟩

end FrobA
p2m_reactivate "P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA.Twist P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.FrobA"

open FrobA in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (C : AddSubgroup W.toAffine.Point) (hC : IsAddCyclic C) (hCN : Nat.card C = N)
    (w : Place κ ↥(modularFunctionFieldC κ N))
    (hw : w.toValuationSubring =
      (moduliPlace κ N W C).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    (frobOnPlacesGeomLevel κ N data hKr w).toValuationSubring =
      (moduliPlace κ N (W.map (frobenius κ q'))
          (C.map (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W)))).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom := by
  classical
  haveI : PerfectField κ := IsAlgClosed.perfectField κ

  rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q' κ N data hKr w]

  obtain ⟨σ, hσ, hσbase, hσincl⟩ := FrobA.exists_fullArithFrob κ q' N

  have hincl : ∀ x : ↥(modularFunctionFieldC κ N),
      σ • (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)) x = (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)) (arithFrobC q' κ N • x) := fun x => (hσincl x).symm

  have hNκ : (N : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)

  have key : σ • moduliPlace κ N W C =
      moduliPlace κ N (W.map (frobenius κ q')) (C.map (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W))) := by

    obtain ⟨gC, hgC⟩ := IsAddCyclic.exists_generator (α := ↥C)
    have hCg : C = AddSubgroup.zmultiples (gC : W.toAffine.Point) := by
      refine le_antisymm (fun y hy => ?_) (AddSubgroup.zmultiples_le_of_mem gC.2)
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgC ⟨y, hy⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hg : addOrderOf (gC : W.toAffine.Point) = N := by
      rw [← Nat.card_zmultiples (gC : W.toAffine.Point), ← hCg, hCN]

    let P : Gamma0Pair N κ := ⟨W, inferInstance, (gC : W.toAffine.Point), hg⟩
    let P' : Gamma0Pair N κ := P.map (frobenius κ q')
    have hgen : P'.gen = WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W) (gC : W.toAffine.Point) := by
      show WeierstrassCurve.mapPointHom (frobenius κ q') (W₀ := W) (gC : W.toAffine.Point) = _
      rw [WeierstrassCurve.mapPointHom_eq_ratPointHom]
    have hC' : C.map (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W)) = AddSubgroup.zmultiples P'.gen := by
      rw [hCg, AddMonoidHom.map_zmultiples, hgen]
      rfl

    have h1 : IsModuliPlaceOf κ N (Quot.mk _ P) (moduliPlace κ N W C) := by
      rw [hCg]
      exact isModuliPlaceOf_moduliPlace κ N W (gC : W.toAffine.Point) hg (isModuliPlaceOf_nonempty κ N hNκ _)
    have h2 := ModularCurve.isModuliPlaceOf_map_frobenius_smul q' N σ hσ _ _ h1
    rw [ModuliPoint.map_mk] at h2
    have h3 : IsModuliPlaceOf κ N (Quot.mk _ P')
        (moduliPlace κ N (W.map (frobenius κ q')) (C.map (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W)))) := by
      rw [hC']
      exact isModuliPlaceOf_moduliPlace κ N P'.toCurve P'.gen P'.addOrderOf_gen (isModuliPlaceOf_nonempty κ N hNκ _)
    exact ModularCurve.eq_of_isModuliPlaceOf κ N hNκ _ _ _ h2 h3

  rw [key.symm]
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_comap,
    AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hw, ValuationSubring.mem_comap]
  have hx : (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom ((arithFrobC q' κ N)⁻¹ • x) = σ⁻¹ • (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom x := by
    rw [eq_inv_smul_iff]
    show σ • (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)) ((arithFrobC q' κ N)⁻¹ • x) = (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)) x
    rw [hincl, smul_inv_smul]
  rw [hx]

end S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
end P2MW
export P2MW.S_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius (solution)
