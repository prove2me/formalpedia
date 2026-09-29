-- Prove2me | solution 1 for ModularCurve.existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/91fa874a-c331-5771-9823-d9a9a05c65f6

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve WeierstrassCurve"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC ssPlaces mem_ssPlaces_iff jGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace ssJSet ModuliPoint IsModuliPlaceOf moduliPlace isModuliPlaceOf_moduliPlace modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full moduliPlace_orbitClauses eq_of_isModuliPlaceOf isModuliPlaceOf_nonempty modularFunctionFieldC_eq_modularFunctionFieldFullC isAffineGeomPlace_or_ord_jGeomGen_lt_zero"
namespace SSPlacesModuli
p2m_open "ModularCurve"

section PlaceCalculus

variable {K F G : Type*} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

theorem algebraMap_comm (e : F ≃ₐ[K] G) (a : K) :
    e.toRingEquiv (algebraMap K F a) = algebraMap K G a :=
  e.commutes a

abbrev transport (e : F ≃ₐ[K] G) : Place K F → Place K G :=
  Place.congrRingEquiv e.toRingEquiv (algebraMap_comm e)

theorem mem_transport_iff (e : F ≃ₐ[K] G) (v : Place K F) (y : G) :
    y ∈ (transport e v).toValuationSubring ↔ e.symm y ∈ v.toValuationSubring :=
  Iff.rfl

theorem transport_injective (e : F ≃ₐ[K] G) : Function.Injective (transport e) :=
  (Place.congrEquiv e.toRingEquiv (algebraMap_comm e)).injective

theorem ord_transport (e : F ≃ₐ[K] G) (v : Place K F) (f : F) :
    (transport e v).ord (e f) = v.ord f :=
  Place.ord_congrRingEquiv e.toRingEquiv (algebraMap_comm e) v f

theorem transport_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) :
    transport e (transport e.symm P) = P := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_transport_iff, mem_transport_iff, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

theorem transport_symm_transport (e : F ≃ₐ[K] G) (P : Place K F) :
    transport e.symm (transport e P) = P := by
  have h := transport_transport_symm e.symm P
  rwa [AlgEquiv.symm_symm] at h

theorem ord_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) (f : F) :
    (transport e.symm P).ord f = P.ord (e f) := by
  conv_rhs => rw [← transport_transport_symm e P]
  rw [ord_transport]

end PlaceCalculus

section Ident

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jF : ((jF K N : modularFunctionFieldFullC K N) : LaurentSeries K) = jqModC K := rfl

theorem coe_equivOfEq {L : Type*} [Field L] [Algebra K L] {S T : IntermediateField K L}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : L) = x := rfl

variable {K N}
variable (hqN : ¬ ringChar K ∣ N)

include hqN in

theorem fieldC_eq : modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
  ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N hqN

def eC : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldC K N :=
  IntermediateField.equivOfEq (fieldC_eq hqN).symm

@[scoped simp] theorem coe_eC (x : modularFunctionFieldFullC K N) :
    ((eC hqN x : modularFunctionFieldC K N) : LaurentSeries K) = x :=
  coe_equivOfEq K (fieldC_eq hqN).symm x

theorem coe_eC_symm (x : modularFunctionFieldC K N) :
    (((eC hqN).symm x : modularFunctionFieldFullC K N) : LaurentSeries K) = x := by
  rw [← coe_eC hqN ((eC hqN).symm x), AlgEquiv.apply_symm_apply]

theorem eC_jF : eC hqN (jF K N) = jGeomGen K N :=
  Subtype.ext (coe_eC hqN (jF K N))

theorem eC_jF_sub (c : K) :
    eC hqN (jF K N - algebraMap K (modularFunctionFieldFullC K N) c) =
      jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c := by
  rw [map_sub, AlgEquiv.commutes, eC_jF]

theorem transport_eC_eq_iff (v : Place K (modularFunctionFieldFullC K N)) (x : Place K (modularFunctionFieldC K N)) :
    x = transport (eC hqN) v ↔
      x.toValuationSubring = v.toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full K N)).toRingHom := by
  constructor
  · rintro rfl
    refine SetLike.ext fun y => ?_
    rw [mem_transport_iff, ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ v.toValuationSubring) (Subtype.ext rfl))
  · intro h
    ext1
    rw [h]
    refine SetLike.ext fun y => ?_
    rw [mem_transport_iff, ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ v.toValuationSubring) (Subtype.ext rfl))

theorem ordC (c : K) (v : Place K (modularFunctionFieldFullC K N)) :
    (transport (eC hqN) v).ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c) =
      v.ord (jF K N - algebraMap K (modularFunctionFieldFullC K N) c) := by
  rw [← eC_jF_sub hqN, ord_transport]

end Ident

section Moduli

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem huniq_of (M : ℕ) [NeZero M] (hM : (M : κ) ≠ 0) :
    ∀ (x : ModuliPoint M κ) (v v' : Place κ (modularFunctionFieldFullC κ M)),
      IsModuliPlaceOf κ M x v → IsModuliPlaceOf κ M x v' → v = v' :=
  fun x v v' hv hv' => ModularCurve.eq_of_isModuliPlaceOf κ M hM x v v' hv hv'

end Moduli

section Rational

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

theorem isRational_of_toValuationSubring_eq_comap (P : Place K F) (W : Place K Ω) (φ : F →+* Ω)
    (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K Ω c)
    (h : P.toValuationSubring = W.toValuationSubring.comap φ) (hW : W.IsRational) : P.IsRational := by
  have hmem : ∀ y : F, y ∈ P.toValuationSubring → φ y ∈ W.toValuationSubring := fun y hy => by
    rw [h] at hy
    exact hy

  let φ' : P.toValuationSubring →+* W.toValuationSubring :=
    (φ.comp P.toValuationSubring.subtype).codRestrict W.toValuationSubring (fun y => hmem (y : F) y.2)
  have hφ'c : ∀ c : K, φ' (algebraMap K P.toValuationSubring c) = algebraMap K W.toValuationSubring c := fun c =>
    Subtype.ext (by
      show φ ((algebraMap K P.toValuationSubring c : P.toValuationSubring) : F) = (algebraMap K W.toValuationSubring c : Ω)
      rw [Place.coe_algebraMap, Place.coe_algebraMap, hφ])
  intro b
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective b
  obtain ⟨c, hc⟩ := hW (IsLocalRing.residue W.toValuationSubring (φ' y))
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply K P.toValuationSubring P.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsScalarTower.algebraMap_apply K W.toValuationSubring W.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc
  intro hu
  apply hc
  have : φ' (algebraMap K P.toValuationSubring c - y) = algebraMap K W.toValuationSubring c - φ' y := by
    rw [map_sub, hφ'c]
  rw [← this]
  exact hu.map φ'

end Rational

section Subgroups

variable {G : Type*} [AddCommGroup G]

theorem exists_zmultiples_eq (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ) (hn : Nat.card C = n) :
    ∃ P : G, AddSubgroup.zmultiples P = C ∧ addOrderOf P = n := by
  obtain ⟨P, hP⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨P, hP, ?_⟩
  rw [← Nat.card_zmultiples, hP, hn]

end Subgroups

end ModularCurve.SSPlacesModuli
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve.SSPlacesModuli"
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace.ModularCurve.SSPlacesModuli"

open ModularCurve.SSPlacesModuli in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (E : WeierstrassCurve κ) [E.IsElliptic] (hssE : ∀ P : E.toAffine.Point, q' • P = 0 → P = 0)
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = N) :
    ∃! w : Place κ ↥(modularFunctionFieldC κ N), w ∈ ssPlaces q' N κ ∧
      w.toValuationSubring = (moduliPlace κ N E C).toValuationSubring.comap (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom := by
  have hN : (N : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)
  have hqN : ¬ ringChar κ ∣ N := by rw [ringChar.eq κ q']; exact hq'N

  set v := moduliPlace κ N E C with hvdef
  set w := transport (eC hqN) v with hwdef
  have hw : w.toValuationSubring =
      v.toValuationSubring.comap (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom :=
    (transport_eC_eq_iff hqN v w).mp rfl

  have hord : 0 < w.ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) := by
    rw [hwdef, ordC]
    exact (ModularCurve.moduliPlace_orbitClauses κ N hN (huniq_of N hN)).1 E ⟨C, hC⟩
  have hjmem : jGeomGen κ N ∈ w.toValuationSubring := by
    have hmem : jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j ∈ w.toValuationSubring :=
      w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero κ N E.j) hord.le
    have := add_mem hmem (w.algebraMap_mem' E.j)
    rwa [sub_add_cancel] at this

  have haff : IsAffineGeomPlace κ N w :=
    (ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero κ N w).resolve_right (not_lt.mpr (w.ord_nonneg_of_mem hjmem))

  have heval : w.evalAt (jGeomGen κ N) = E.j := by
    have hcongr := w.evalAt_congr hjmem (w.algebraMap_mem' E.j) (Or.inr hord)
    rw [hcongr, w.evalAt_algebraMap]
  have hj : w.evalAt (jGeomGen κ N) ∈ ssJSet q' κ := by
    rw [heval]
    exact WeierstrassCurve.j_mem_ssJSet_of_forall_smul_eq_zero q' E hssE

  have hrat : w.IsRational := by
    obtain ⟨g, hgC, hg⟩ := exists_zmultiples_eq C hC.1 N hC.2
    have hmod : IsModuliPlaceOf κ N _ (moduliPlace κ N E (AddSubgroup.zmultiples g)) :=
      isModuliPlaceOf_moduliPlace κ N E g hg (ModularCurve.isModuliPlaceOf_nonempty κ N hN _)
    rw [hgC] at hmod
    obtain ⟨Ω, _iΩ, _dΩ, _aΩ, D, hD⟩ := hmod
    have hWrat : D.W.IsRational := fun b => ⟨D.res b, D.algebraMap_res b⟩
    have hcomb : w.toValuationSubring = D.W.toValuationSubring.comap
        (D.emb.toRingHom.comp (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) := by
      rw [hw, hvdef, hD, ValuationSubring.comap_comap]
    exact isRational_of_toValuationSubring_eq_comap w D.W _
      (fun c => (D.emb.comp (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N))).commutes c) hcomb hWrat

  refine ⟨w, ⟨(mem_ssPlaces_iff q' N κ).mpr ⟨hrat, haff, hj⟩, hw⟩, fun w' hw' => ?_⟩
  exact (transport_eC_eq_iff hqN v w').mpr hw'.2

end S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace
end P2MW
export P2MW.S_ModularCurve_existsUnique_mem_ssPlaces_toValuationSubring_eq_comap_moduliPlace (solution)
