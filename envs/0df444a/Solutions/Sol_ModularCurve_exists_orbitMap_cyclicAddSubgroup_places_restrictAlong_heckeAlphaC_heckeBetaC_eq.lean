-- Prove2me | solution 1 for ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cc4c205e-c4c7-5ec9-abd2-702f73bcd759

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_ModuliPlace
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_inclusion
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

noncomputable section

namespace P2MKcDegenOrbit

section PlaceCalculus

variable {K F F' G G' : Type*} [Field K] [Field F] [Field F'] [Field G] [Field G']
  [Algebra K F] [Algebra K F'] [Algebra K G] [Algebra K G']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (x : F) : x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

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

theorem restrictAlong_transport (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (v : Place K F') :
    (transport e₂ v).restrictAlong φ hφ = transport e₁ (v.restrictAlong φ' hφ') := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_restrictAlong_iff, mem_transport_iff, mem_transport_iff, mem_restrictAlong_iff]
  have hy : φ y = e₂ (φ' (e₁.symm y)) := by
    rw [← hcomm, AlgEquiv.apply_symm_apply]
  rw [hy, AlgEquiv.symm_apply_apply]

theorem isIntegral_of_comm (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) : φ'.toRingHom.IsIntegral := by
  have h : φ'.toRingHom =
      (e₂.symm : G' →+* F').comp (φ.toRingHom.comp (e₁ : F →+* G)) := by
    ext x
    show φ' x = e₂.symm (φ (e₁ x))
    rw [hcomm, AlgEquiv.symm_apply_apply]
  rw [h]
  refine RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ?_ hφ) ?_
  · exact RingHom.isIntegral_of_surjective _ e₁.surjective
  · exact RingHom.isIntegral_of_surjective _ e₂.symm.surjective

end PlaceCalculus

section Tower

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

scoped instance neZero_mul : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩

def jF (N : ℕ) [NeZero N] : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jF (N : ℕ) [NeZero N] : ((jF K N : modularFunctionFieldFullC K N) :
    LaurentSeries K) = jqModC K := rfl

def inclMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  IntermediateField.inclusion (full_degeneracyC_le K (dvd_mul_right M s))

@[scoped simp] theorem coe_inclMS (x : modularFunctionFieldFullC K M) :
    ((inclMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) = x :=
  IntermediateField.coe_inclusion _ x

def betaMSRingHom : modularFunctionFieldFullC K M →+* modularFunctionFieldFullC K (M * s) where
  toFun x := ⟨qExpand K s (x : LaurentSeries K),
    full_degeneracyC_map_le K M s ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand K s))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K s) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K s))
  map_add' _ _ := Subtype.ext (map_add (qExpand K s) _ _)

def betaMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  { betaMSRingHom K M s with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K s (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem coe_betaMS (x : modularFunctionFieldFullC K M) :
    ((betaMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
      qExpand K s (x : LaurentSeries K) := rfl

end Tower

section Hypotheses

variable (K : Type*) [Field K] [DecidableEq K]

abbrev CycSub (E : WeierstrassCurve K) (N : ℕ) : Type _ :=
  {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N}

abbrev OrbFamily : Type _ :=
  ∀ (N : ℕ) [NeZero N] (E : WeierstrassCurve K),
    AddSubgroup E.toAffine.Point → Place K (modularFunctionFieldFullC K N)

variable {K}

def OrbitClauses (π : OrbFamily K) (N : ℕ) [NeZero N] : Prop :=
  (∀ (E : WeierstrassCurve K) [E.IsElliptic] (C : CycSub K E N),
      0 < (π N E C.1).ord (jF K N - algebraMap K (modularFunctionFieldFullC K N) E.j)) ∧
  (∀ (E : WeierstrassCurve K) [E.IsElliptic] (P : Place K (modularFunctionFieldFullC K N)),
      0 < P.ord (jF K N - algebraMap K (modularFunctionFieldFullC K N) E.j) →
        ∃ C : CycSub K E N, π N E C.1 = P) ∧
  (∀ (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
      (C : CycSub K E N) (C' : CycSub K E' N),
      π N E C.1 = π N E' C'.1 ↔ ∃ γ : VariableChange K, γ • E = E' ∧
        ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') ∧
  (∀ (E : WeierstrassCurve K) [E.IsElliptic] (C : CycSub K E N),
      (π N E C.1).ord (jF K N - algebraMap K (modularFunctionFieldFullC K N) E.j) =
        (Nat.card {C' : CycSub K E N // π N E C'.1 = π N E C.1} : ℤ))

variable (M s : ℕ) [NeZero M] [NeZero s] (E₀ : WeierstrassCurve K)

def AlphaLaw (π : OrbFamily K) : Prop :=
  ∀ (hι : (inclMS K M s).toRingHom.IsIntegral)
    (C : CycSub K E₀ (M * s)) (C' : CycSub K E₀ M), (∀ T ∈ C.1, s • T ∈ C'.1) →
      (π (M * s) E₀ C.1).restrictAlong (inclMS K M s) hι = π M E₀ C'.1

def BetaLawFull (π : OrbFamily K) : Prop :=
  ∀ (hb : (betaMS K M s).toRingHom.IsIntegral)
    (C : CycSub K E₀ (M * s)) (Q : E₀.toAffine.Point), Q ∈ C.1 → addOrderOf Q = s →
    (E₀.fullKernelQuotient Q s).Δ ≠ 0 →
    ∀ φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q s).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q →
      (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
        (φ P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
              ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
              ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
      ∀ C'' : CycSub K (E₀.fullKernelQuotient Q s) M, (∀ T ∈ C.1, φ T ∈ C''.1) →
        (π (M * s) E₀ C.1).restrictAlong (betaMS K M s) hb = π M (E₀.fullKernelQuotient Q s) C''.1

def BetaLawVelu (π : OrbFamily K) : Prop :=
  ∀ (hb : (betaMS K M s).toRingHom.IsIntegral)
    (C : CycSub K E₀ (M * s)) (n : ℕ) (Q : E₀.toAffine.Point), s = 2 * n + 1 → Q ∈ C.1 →
    addOrderOf Q = 2 * n + 1 →
    (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0 →
    ∀ φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q →
      (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
        (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
            (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h') →
      ∀ C'' : CycSub K (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) M,
        (∀ T ∈ C.1, φ T ∈ C''.1) →
          (π (M * s) E₀ C.1).restrictAlong (betaMS K M s) hb =
            π M (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C''.1

end Hypotheses

section Identifications

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

theorem coe_equivOfEq {L : Type*} [Field L] [Algebra K L] {S T : IntermediateField K L}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : L) = x := rfl

variable {K M s} in

theorem not_dvd_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) :
    ¬ ringChar K ∣ M * s ∧ ¬ ringChar K ∣ M := by
  have h1 : ¬ ringChar K ∣ M * s := fun h => hMs ((ringChar.spec K (M * s)).mpr h)
  exact ⟨h1, fun h => h1 (h.mul_right s)⟩

variable {K M s} in

theorem fieldC_eq (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldC K M = modularFunctionFieldFullC K M :=
  ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) M
    (not_dvd_of_cast_mul_ne_zero hMs).2

variable {K M s} in

theorem roof_eq (hMs : ((M * s : ℕ) : K) ≠ 0) :
    charLDegeneracyRoof K M s = modularFunctionFieldFullC K (M * s) :=
  ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K (ringChar K) M s
    (not_dvd_of_cast_mul_ne_zero hMs).1

variable {K M s} in

def eC (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldFullC K M ≃ₐ[K] modularFunctionFieldC K M :=
  IntermediateField.equivOfEq (fieldC_eq hMs).symm

variable {K M s} in

def eR (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldFullC K (M * s) ≃ₐ[K] charLDegeneracyRoof K M s :=
  IntermediateField.equivOfEq (roof_eq hMs).symm

variable {K M s} (hMs : ((M * s : ℕ) : K) ≠ 0)

@[scoped simp] theorem coe_eC (x : modularFunctionFieldFullC K M) :
    ((eC hMs x : modularFunctionFieldC K M) : LaurentSeries K) = x :=
  coe_equivOfEq K (fieldC_eq hMs).symm x

@[scoped simp] theorem coe_eR (x : modularFunctionFieldFullC K (M * s)) :
    ((eR hMs x : charLDegeneracyRoof K M s) : LaurentSeries K) = x :=
  coe_equivOfEq K (roof_eq hMs).symm x

theorem eC_jF : eC hMs (jF K M) = jGeomGen K M :=
  Subtype.ext (coe_eC hMs (jF K M))

theorem eR_jF : eR hMs (jF K (M * s)) = heckeAlphaC K M s (jGeomGen K M) := by
  apply Subtype.ext
  rw [coe_eR, coe_heckeAlphaC, coe_jF, coe_jGeomGen]

theorem heckeAlphaC_eC (x : modularFunctionFieldFullC K M) :
    heckeAlphaC K M s (eC hMs x) = eR hMs (inclMS K M s x) := by
  apply Subtype.ext
  rw [coe_heckeAlphaC, coe_eC, coe_eR, coe_inclMS]

theorem heckeBetaC_eC (x : modularFunctionFieldFullC K M) :
    heckeBetaC K M s (eC hMs x) = eR hMs (betaMS K M s x) := by
  apply Subtype.ext
  rw [coe_heckeBetaC, coe_eC, coe_eR, coe_betaMS]

theorem eC_jF_sub (c : K) :
    eC hMs (jF K M - algebraMap K (modularFunctionFieldFullC K M) c) =
      jGeomGen K M - algebraMap K (modularFunctionFieldC K M) c := by
  rw [map_sub, AlgEquiv.commutes, eC_jF]

theorem eR_jF_sub (c : K) :
    eR hMs (jF K (M * s) - algebraMap K (modularFunctionFieldFullC K (M * s)) c) =
      heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) c := by
  rw [map_sub, AlgEquiv.commutes, eR_jF]

end Identifications

section Assembly

variable {K F G : Type*} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

theorem transport_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) :
    transport e (transport e.symm P) = P := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_transport_iff, mem_transport_iff, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

theorem ord_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) (f : F) :
    (transport e.symm P).ord f = P.ord (e f) := by
  conv_rhs => rw [← transport_transport_symm e P]
  rw [ord_transport]

theorem natCard_fibre_comp {X : Type*} (ι : Place K F → Place K G) (hι : Function.Injective ι)
    (p : X → Place K F) (x : X) :
    Nat.card {x' : X // ι (p x') = ι (p x)} = Nat.card {x' : X // p x' = p x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => hι.eq_iff)

end Assembly

section Main

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution_of
    (hs : s.Prime) (hMs : ((M * s : ℕ) : K) ≠ 0)
    (hα : HeckeAlphaCIntegral K M s) (hβ : HeckeBetaCIntegral K M s)
    (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)
    (π : OrbFamily K) (hgM : OrbitClauses π M) (hgMs : OrbitClauses π (M * s))
    (hA : AlphaLaw M s E₀ π) (hBv : BetaLawVelu M s E₀ π) (hBf : BetaLawFull M s E₀ π) :
    ∃ (g : ∀ E : WeierstrassCurve K,
          {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} →
            Place K (modularFunctionFieldC K M))
      (f : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} →
          Place K (charLDegeneracyRoof K M s)),

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          0 < (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j)) ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic] (P : Place K (modularFunctionFieldC K M)),
          0 < P.ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) →
            ∃ C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}, g E C = P) ∧

      (∀ (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
          (C' : {C : AddSubgroup E'.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          g E C = g E' C' ↔ ∃ γ : VariableChange K, γ • E = E' ∧
            ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) =
            (Nat.card {C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} //
              g E C' = g E C} : ℤ)) ∧

      (∀ C, 0 < (f C).ord (heckeAlphaC K M s (jGeomGen K M) -
          algebraMap K (charLDegeneracyRoof K M s) j₀)) ∧

      (∀ P : Place K (charLDegeneracyRoof K M s),
          0 < P.ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) →
            ∃ C, f C = P) ∧

      (∀ C C', f C = f C' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧

      (∀ C, (f C).ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) =
          (Nat.card {C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} //
            f C' = f C} : ℤ)) ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (∀ T ∈ C.1, s • T ∈ C'.1) →
            (f C).restrictAlong (heckeAlphaC K M s) hα = g E₀ C') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (n : ℕ) (Q : E₀.toAffine.Point), s = 2 * n + 1 → Q ∈ C.1 → addOrderOf Q = 2 * n + 1 →
        (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
            (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
              ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
                (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h') →
          ∀ C'' : {C : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ =
                g (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C'') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (Q : E₀.toAffine.Point), Q ∈ C.1 → addOrderOf Q = s →
        (E₀.fullKernelQuotient Q s).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q s).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
            (φ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
          ∀ C'' : {C : AddSubgroup (E₀.fullKernelQuotient Q s).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ = g (E₀.fullKernelQuotient Q s) C'') := by

  let g : ∀ E : WeierstrassCurve K,
      {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} →
        Place K (modularFunctionFieldC K M) := fun E C => transport (eC hMs) (π M E C.1)
  let f : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} →
      Place K (charLDegeneracyRoof K M s) := fun C => transport (eR hMs) (π (M * s) E₀ C.1)
  have hg : ∀ (E : WeierstrassCurve K) C, g E C = transport (eC hMs) (π M E C.1) := fun _ _ => rfl
  have hf : ∀ C, f C = transport (eR hMs) (π (M * s) E₀ C.1) := fun _ => rfl

  have hι : (inclMS K M s).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC hMs) (eR hMs) (heckeAlphaC K M s) (inclMS K M s) (heckeAlphaC_eC hMs) hα
  have hb : (betaMS K M s).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC hMs) (eR hMs) (heckeBetaC K M s) (betaMS K M s) (heckeBetaC_eC hMs) hβ

  have ordC : ∀ (c : K) (v : Place K (modularFunctionFieldFullC K M)),
      (transport (eC hMs) v).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) c) =
        v.ord (jF K M - algebraMap K (modularFunctionFieldFullC K M) c) := by
    intro c v
    rw [← eC_jF_sub hMs, ord_transport]
  have ordR : ∀ (v : Place K (modularFunctionFieldFullC K (M * s))),
      (transport (eR hMs) v).ord (heckeAlphaC K M s (jGeomGen K M) -
          algebraMap K (charLDegeneracyRoof K M s) j₀) =
        v.ord (jF K (M * s) - algebraMap K (modularFunctionFieldFullC K (M * s)) E₀.j) := by
    intro v
    rw [← eR_jF_sub hMs, ord_transport, hE₀]
  obtain ⟨hM1, hM2, hM3, hM4⟩ := hgM
  obtain ⟨hN1, hN2, hN3, hN4⟩ := hgMs
  refine ⟨g, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro E _ C
    rw [hg, ordC]
    exact hM1 E C
  ·
    intro E _ P hP
    have hP' : 0 < (transport (eC hMs).symm P).ord
        (jF K M - algebraMap K (modularFunctionFieldFullC K M) E.j) := by
      rwa [ord_transport_symm, eC_jF_sub]
    obtain ⟨C, hC⟩ := hM2 E _ hP'
    exact ⟨C, by rw [hg, hC, transport_transport_symm]⟩
  ·
    intro E E' _ _ C C'
    rw [hg, hg, (transport_injective (eC hMs)).eq_iff]
    exact hM3 E E' C C'
  ·
    intro E _ C
    rw [hg, ordC, hM4 E C]
    congr 1
    exact (natCard_fibre_comp (transport (eC hMs)) (transport_injective (eC hMs))
      (fun C' : CycSub K E M => π M E C'.1) C).symm
  ·
    intro C
    rw [hf, ordR]
    exact hN1 E₀ C
  ·
    intro P hP
    have hP' : 0 < (transport (eR hMs).symm P).ord
        (jF K (M * s) - algebraMap K (modularFunctionFieldFullC K (M * s)) E₀.j) := by
      rwa [ord_transport_symm, eR_jF_sub, hE₀]
    obtain ⟨C, hC⟩ := hN2 E₀ _ hP'
    exact ⟨C, by rw [hf, hC, transport_transport_symm]⟩
  ·
    intro C C'
    rw [hf, hf, (transport_injective (eR hMs)).eq_iff]
    exact hN3 E₀ E₀ C C'
  ·
    intro C
    rw [hf, ordR, hN4 E₀ C]
    congr 1
    exact (natCard_fibre_comp (transport (eR hMs)) (transport_injective (eR hMs))
      (fun C' : CycSub K E₀ (M * s) => π (M * s) E₀ C'.1) C).symm
  ·
    intro C C' hCC'
    rw [hf, hg, restrictAlong_transport (eC hMs) (eR hMs) (heckeAlphaC K M s) (inclMS K M s)
      (heckeAlphaC_eC hMs) hα hι]
    exact congrArg (transport (eC hMs)) (hA hι C C' hCC')
  ·
    intro C n Q hsn hQC hQ hΔ φ hker hφ C'' hC''
    rw [hf, hg, restrictAlong_transport (eC hMs) (eR hMs) (heckeBetaC K M s) (betaMS K M s)
      (heckeBetaC_eC hMs) hβ hb]
    exact congrArg (transport (eC hMs)) (hBv hb C n Q hsn hQC hQ hΔ φ hker hφ C'' hC'')
  ·
    intro C Q hQC hQ hΔ φ hker hφ C'' hC''
    rw [hf, hg, restrictAlong_transport (eC hMs) (eR hMs) (heckeBetaC K M s) (betaMS K M s)
      (heckeBetaC_eC hMs) hβ hb]
    exact congrArg (transport (eC hMs)) (hBf hb C Q hQC hQ hΔ φ hker hφ C'' hC'')

end Main

section ModuliPlace

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K]

abbrev modPi : OrbFamily K := fun N _ E C => moduliPlace K N E C

theorem modPi_apply (N : ℕ) [NeZero N] (E : WeierstrassCurve K)
    (C : AddSubgroup E.toAffine.Point) : modPi K N E C = moduliPlace K N E C := rfl

variable (N : ℕ) [NeZero N]

theorem hex_of (hN : (N : K) ≠ 0) : ∀ x : ModuliPoint N K, ∃ v, IsModuliPlaceOf K N x v :=
  fun x => ModularCurve.isModuliPlaceOf_nonempty K N hN x

theorem huniq_of (hN : (N : K) ≠ 0) :
    ∀ (x : ModuliPoint N K) (v v' : Place K (modularFunctionFieldFullC K N)),
      IsModuliPlaceOf K N x v → IsModuliPlaceOf K N x v' → v = v' :=
  fun x v v' hv hv' => ModularCurve.eq_of_isModuliPlaceOf K N hN x v v' hv hv'

theorem orbitClauses_modPi (hN : (N : K) ≠ 0) : OrbitClauses (modPi K) N :=
  ModularCurve.moduliPlace_orbitClauses K N hN (huniq_of K N hN)

variable {N} (M s : ℕ) [NeZero M] [NeZero s]

variable {K M s} in

theorem cast_ne_zero_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) : (M : K) ≠ 0 := by
  intro h
  apply hMs
  rw [Nat.cast_mul, h, zero_mul]

theorem alphaLaw_modPi (hMs : ((M * s : ℕ) : K) ≠ 0) (E₀ : WeierstrassCurve K) :
    AlphaLaw M s E₀ (modPi K) := by
  intro hι C C' hCC'
  have hq : M * s / M = s := Nat.mul_div_cancel_left s (Nat.pos_of_ne_zero (NeZero.ne M))
  have hCC'' : ∀ T ∈ C.1, (M * s / M) • T ∈ C'.1 := fun T hT => by
    rw [hq]
    exact hCC' T hT
  exact ModularCurve.moduliPlace_restrictAlong_inclusion K (M * s) M (dvd_mul_right M s)
    (hex_of K (M * s) hMs) (huniq_of K M (cast_ne_zero_of_cast_mul_ne_zero hMs)) hι E₀ C C' hCC''

theorem betaLawFull_modPi (hMs : ((M * s : ℕ) : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    BetaLawFull M s E₀ (modPi K) := by
  intro hb C Q hQC hQ hΔ φ hker hφ C'' hCC''
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient K M s hMs
    (huniq_of K M (cast_ne_zero_of_cast_mul_ne_zero hMs)) (hex_of K (M * s) hMs)
    (betaMS K M s) (fun f => rfl) hb E₀ C.1 C.2 Q hQC hQ hΔ φ hker hφ C''.1 C''.2 hCC''

theorem betaLawVelu_modPi (hMs : ((M * s : ℕ) : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    BetaLawVelu M s E₀ (modPi K) := by
  intro hb C n Q hsn hQC hQ hΔ φ hker hφ C'' hCC''
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient K M s hMs
    (huniq_of K M (cast_ne_zero_of_cast_mul_ne_zero hMs)) (hex_of K (M * s) hMs)
    (betaMS K M s) (fun f => rfl) hb E₀ C.1 C.2 n hsn Q hQC hQ hΔ φ hker hφ C''.1 C''.2 hCC''

end ModuliPlace

end P2MKcDegenOrbit
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq.P2MKcDegenOrbit"

open P2MKcDegenOrbit in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (hs : s.Prime) (hMs : ((M * s : ℕ) : K) ≠ 0)
    (hα : HeckeAlphaCIntegral K M s) (hβ : HeckeBetaCIntegral K M s)
    (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) :
    ∃ (g : ∀ E : WeierstrassCurve K,
          {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} →
            Place K (modularFunctionFieldC K M))
      (f : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} →
          Place K (charLDegeneracyRoof K M s)),

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          0 < (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j)) ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic] (P : Place K (modularFunctionFieldC K M)),
          0 < P.ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) →
            ∃ C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}, g E C = P) ∧

      (∀ (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
          (C' : {C : AddSubgroup E'.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          g E C = g E' C' ↔ ∃ γ : VariableChange K, γ • E = E' ∧
            ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) =
            (Nat.card {C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} //
              g E C' = g E C} : ℤ)) ∧

      (∀ C, 0 < (f C).ord (heckeAlphaC K M s (jGeomGen K M) -
          algebraMap K (charLDegeneracyRoof K M s) j₀)) ∧

      (∀ P : Place K (charLDegeneracyRoof K M s),
          0 < P.ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) →
            ∃ C, f C = P) ∧

      (∀ C C', f C = f C' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧

      (∀ C, (f C).ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) =
          (Nat.card {C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} //
            f C' = f C} : ℤ)) ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (∀ T ∈ C.1, s • T ∈ C'.1) →
            (f C).restrictAlong (heckeAlphaC K M s) hα = g E₀ C') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (n : ℕ) (Q : E₀.toAffine.Point), s = 2 * n + 1 → Q ∈ C.1 → addOrderOf Q = 2 * n + 1 →
        (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
            (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
              ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
                (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h') →
          ∀ C'' : {C : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ =
                g (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C'') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (Q : E₀.toAffine.Point), Q ∈ C.1 → addOrderOf Q = s →
        (E₀.fullKernelQuotient Q s).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q s).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
            (φ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
          ∀ C'' : {C : AddSubgroup (E₀.fullKernelQuotient Q s).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ = g (E₀.fullKernelQuotient Q s) C'') :=
  solution_of K M s hs hMs hα hβ j₀ E₀ hE₀ (modPi K)
    (orbitClauses_modPi K M (cast_ne_zero_of_cast_mul_ne_zero hMs))
    (orbitClauses_modPi K (M * s) hMs)
    (alphaLaw_modPi K M s hMs E₀) (betaLawVelu_modPi K M s hMs E₀) (betaLawFull_modPi K M s hMs E₀)

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq.P2MKcDegenOrbit"

end S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
end P2MW
export P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq (solution)
