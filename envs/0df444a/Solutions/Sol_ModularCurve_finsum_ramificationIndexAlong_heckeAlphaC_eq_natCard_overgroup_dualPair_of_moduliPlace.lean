-- Prove2me | solution 1 for ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a6115a2f-b42f-5269-a246-fe7196e8e151

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_inclusion
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
import Theorems.Thm_WeierstrassCurve_coordsOrZero_veluPointMap2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC algebraMap_laurentSeries_apply_eq_single mem_restrictAlong_iff jqModC modularFunctionFieldC qExpand qExpand_single jGeomGen coe_jGeomGen ModuliPoint IsModuliPlaceOf moduliPlace modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full full_degeneracyC_le full_degeneracyC_map_le moduliPlace_orbitClauses moduliPlace_restrictAlong_inclusion moduliPlace_restrictAlong_qExpand_fullKernelQuotient moduliPlace_restrictAlong_qExpand_veluQuotient isModuliPlaceOf_nonempty eq_of_isModuliPlaceOf modularFunctionFieldC_eq_modularFunctionFieldFullC charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul hasPrincipalDivisors_charLDegeneracyRoof"
namespace TransposeRoofCount
p2m_open "ModularCurve"

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

theorem transport_bijective (e : F ≃ₐ[K] G) : Function.Bijective (transport e) :=
  (Place.congrEquiv e.toRingEquiv (algebraMap_comm e)).bijective

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

theorem ramificationIndexAlong_transport (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x)) (v : Place K F') :
    (transport e₂ v).ramificationIndexAlong φ = v.ramificationIndexAlong φ' := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : G, f ≠ 0 ∧ (transport e₂ v).ord (φ f) = n} =
    sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ v.ord (φ' f) = n}
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨e₁.symm f, by simpa using hf, ?_⟩
    rw [← ord_transport e₂, ← hcomm, AlgEquiv.apply_symm_apply]
    exact hn
  · rintro ⟨f, hf, hn⟩
    refine ⟨e₁ f, by simpa using hf, ?_⟩
    rw [hcomm, ord_transport]
    exact hn

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

theorem natCard_fibre_comp {X : Type*} (ι : Place K F → Place K G) (hι : Function.Injective ι)
    (p : X → Place K F) (x : X) :
    Nat.card {x' : X // ι (p x') = ι (p x)} = Nat.card {x' : X // p x' = p x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => hι.eq_iff)

variable {Z : Type*} [Field Z] [Algebra K Z]

theorem ord_along (φ : F →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (W : Place K Z) (t : F) :
    W.ord (φ t) = W.ramificationIndexAlong φ * (W.restrictAlong φ hφ).ord t := by
  rw [← Place.ord_restrictAlong]

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (W : Place K Z) :
    0 < W.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos

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
  toFun x := ⟨qExpand K s (x : LaurentSeries K), full_degeneracyC_map_le K M s ⟨x, x.2, rfl⟩⟩
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

theorem coe_equivOfEq {L : Type*} [Field L] [Algebra K L] {S T : IntermediateField K L}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : L) = x := rfl

variable {K M s} in
theorem not_dvd_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) :
    ¬ ringChar K ∣ M * s ∧ ¬ ringChar K ∣ M := by
  have h1 : ¬ ringChar K ∣ M * s := fun h => hMs ((ringChar.spec K (M * s)).mpr h)
  exact ⟨h1, fun h => h1 (h.mul_right s)⟩

variable {K M s} in
theorem cast_ne_zero_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) : (M : K) ≠ 0 := by
  intro h
  apply hMs
  rw [Nat.cast_mul, h, zero_mul]

variable {K M s} in
theorem cast_ne_zero_of_cast_mul_ne_zero' (hMs : ((M * s : ℕ) : K) ≠ 0) : (s : K) ≠ 0 := by
  intro h
  apply hMs
  rw [Nat.cast_mul, h, mul_zero]

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

theorem coe_eC_symm (x : modularFunctionFieldC K M) :
    (((eC hMs).symm x : modularFunctionFieldFullC K M) : LaurentSeries K) = x := by
  rw [← coe_eC hMs ((eC hMs).symm x), AlgEquiv.apply_symm_apply]

@[scoped simp] theorem coe_eR (x : modularFunctionFieldFullC K (M * s)) :
    ((eR hMs x : charLDegeneracyRoof K M s) : LaurentSeries K) = x :=
  coe_equivOfEq K (roof_eq hMs).symm x

theorem coe_eR_symm (x : charLDegeneracyRoof K M s) :
    (((eR hMs).symm x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) = x := by
  rw [← coe_eR hMs ((eR hMs).symm x), AlgEquiv.apply_symm_apply]

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

theorem transport_eC_eq_iff (v : Place K (modularFunctionFieldFullC K M)) (x : Place K (modularFunctionFieldC K M)) :
    x = transport (eC hMs) v ↔
      x.toValuationSubring = v.toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full K M)).toRingHom := by
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

end Tower

section Clauses

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

abbrev CycSub (E : WeierstrassCurve κ) (n : ℕ) : Type :=
  {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = n}

variable {N ℓ} (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)

def gPl (E : WeierstrassCurve κ) (C : AddSubgroup E.toAffine.Point) : Place κ (modularFunctionFieldC κ N) :=
  transport (eC hNℓ) (moduliPlace κ N E C)

def fPl (E : WeierstrassCurve κ) (C : AddSubgroup E.toAffine.Point) : Place κ (charLDegeneracyRoof κ N ℓ) :=
  transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C)

include hNℓ in
theorem hN_of : (N : κ) ≠ 0 := cast_ne_zero_of_cast_mul_ne_zero hNℓ

theorem hex_of (M : ℕ) [NeZero M] (hM : (M : κ) ≠ 0) : ∀ x : ModuliPoint M κ, ∃ v, IsModuliPlaceOf κ M x v :=
  fun x => ModularCurve.isModuliPlaceOf_nonempty κ M hM x

theorem huniq_of (M : ℕ) [NeZero M] (hM : (M : κ) ≠ 0) :
    ∀ (x : ModuliPoint M κ) (v v' : Place κ (modularFunctionFieldFullC κ M)),
      IsModuliPlaceOf κ M x v → IsModuliPlaceOf κ M x v' → v = v' :=
  fun x v v' hv hv' => ModularCurve.eq_of_isModuliPlaceOf κ M hM x v v' hv hv'

theorem ordC (c : κ) (v : Place κ (modularFunctionFieldFullC κ N)) :
    (transport (eC hNℓ) v).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) c) =
      v.ord (jF κ N - algebraMap κ (modularFunctionFieldFullC κ N) c) := by
  rw [← eC_jF_sub hNℓ, ord_transport]

theorem ordR (c : κ) (v : Place κ (modularFunctionFieldFullC κ (N * ℓ))) :
    (transport (eR hNℓ) v).ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) c) =
      v.ord (jF κ (N * ℓ) - algebraMap κ (modularFunctionFieldFullC κ (N * ℓ)) c) := by
  rw [← eR_jF_sub hNℓ, ord_transport]

theorem g1 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E N) :
    0 < (gPl hNℓ E C.1).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) := by
  rw [gPl, ordC]
  exact (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).1 E C

theorem g3 (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic] (C : CycSub E N) (C' : CycSub E' N) :
    gPl hNℓ E C.1 = gPl hNℓ E' C'.1 ↔ ∃ γ : VariableChange κ, γ • E = E' ∧
      ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T' := by
  rw [gPl, gPl, (transport_injective (eC hNℓ)).eq_iff]
  exact (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).2.2.1 E E' C C'

theorem g4 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E N) :
    (gPl hNℓ E C.1).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) =
      (Nat.card {C' : CycSub E N // gPl hNℓ E C'.1 = gPl hNℓ E C.1} : ℤ) := by
  have h4 := (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).2.2.2 E C
  have hfib := natCard_fibre_comp (transport (eC hNℓ)) (transport_injective (eC hNℓ))
    (fun C' : CycSub E N => moduliPlace κ N E C'.1) C
  show (transport (eC hNℓ) (moduliPlace κ N E C.1)).ord _ =
    (Nat.card {C' : CycSub E N //
      transport (eC hNℓ) (moduliPlace κ N E C'.1) = transport (eC hNℓ) (moduliPlace κ N E C.1)} : ℤ)
  rw [ordC, hfib]
  exact h4

theorem f2 (E : WeierstrassCurve κ) [E.IsElliptic] (P : Place κ (charLDegeneracyRoof κ N ℓ))
    (hP : 0 < P.ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j)) :
    ∃ C : CycSub E (N * ℓ), fPl hNℓ E C.1 = P := by
  have hP' : 0 < (transport (eR hNℓ).symm P).ord
      (jF κ (N * ℓ) - algebraMap κ (modularFunctionFieldFullC κ (N * ℓ)) E.j) := by
    rwa [ord_transport_symm, eR_jF_sub]
  obtain ⟨C, hC⟩ := (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.1 E _ hP'
  exact ⟨C, by rw [fPl, hC, transport_transport_symm]⟩

theorem f3 (E : WeierstrassCurve κ) [E.IsElliptic] (C C' : CycSub E (N * ℓ)) :
    fPl hNℓ E C.1 = fPl hNℓ E C'.1 ↔ ∃ γ : VariableChange κ, γ • E = E ∧
      ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T' := by
  rw [fPl, fPl, (transport_injective (eR hNℓ)).eq_iff]
  exact (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.2.1 E E C C'

theorem f4 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E (N * ℓ)) :
    (fPl hNℓ E C.1).ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j) =
      (Nat.card {C' : CycSub E (N * ℓ) // fPl hNℓ E C'.1 = fPl hNℓ E C.1} : ℤ) := by
  have h4 := (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.2.2 E C
  have hfib := natCard_fibre_comp (transport (eR hNℓ)) (transport_injective (eR hNℓ))
    (fun C' : CycSub E (N * ℓ) => moduliPlace κ (N * ℓ) E C'.1) C
  show (transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C.1)).ord _ =
    (Nat.card {C' : CycSub E (N * ℓ) //
      transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C'.1) = transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C.1)} : ℤ)
  rw [ordR, hfib]
  exact h4

theorem law_alpha (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (E : WeierstrassCurve κ)
    (C : CycSub E (N * ℓ)) (C' : CycSub E N) (hCC' : ∀ T ∈ C.1, ℓ • T ∈ C'.1) :
    (fPl hNℓ E C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = gPl hNℓ E C'.1 := by
  have hι : (inclMS κ N ℓ).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC hNℓ) (eR hNℓ) (heckeAlphaC κ N ℓ) (inclMS κ N ℓ) (heckeAlphaC_eC hNℓ) hα
  rw [fPl, gPl, restrictAlong_transport (eC hNℓ) (eR hNℓ) (heckeAlphaC κ N ℓ) (inclMS κ N ℓ)
    (heckeAlphaC_eC hNℓ) hα hι]
  congr 1
  have hq : N * ℓ / N = ℓ := Nat.mul_div_cancel_left ℓ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hCC'' : ∀ T ∈ C.1, (N * ℓ / N) • T ∈ C'.1 := fun T hT => by
    rw [hq]
    exact hCC' T hT
  exact ModularCurve.moduliPlace_restrictAlong_inclusion κ (N * ℓ) N (dvd_mul_right N ℓ)
    (hex_of (N * ℓ) hNℓ) (huniq_of N (hN_of hNℓ)) hι E C C' hCC''

theorem law_beta_full (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (C : CycSub E (N * ℓ)) (Q : E.toAffine.Point) (hQC : Q ∈ C.1) (hQ : addOrderOf Q = ℓ)
    (hΔ : (E.fullKernelQuotient Q ℓ).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q ℓ).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (ℓ - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (ℓ - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (C'' : CycSub (E.fullKernelQuotient Q ℓ) N) (hCC'' : ∀ T ∈ C.1, φ T ∈ C''.1) :
    (fPl hNℓ E C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = gPl hNℓ (E.fullKernelQuotient Q ℓ) C''.1 := by
  have hb : (betaMS κ N ℓ).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC hNℓ) (eR hNℓ) (heckeBetaC κ N ℓ) (betaMS κ N ℓ) (heckeBetaC_eC hNℓ) hβ
  rw [fPl, gPl, restrictAlong_transport (eC hNℓ) (eR hNℓ) (heckeBetaC κ N ℓ) (betaMS κ N ℓ)
    (heckeBetaC_eC hNℓ) hβ hb]
  congr 1
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient κ N ℓ hNℓ
    (huniq_of N (hN_of hNℓ)) (hex_of (N * ℓ) hNℓ)
    (betaMS κ N ℓ) (fun f => rfl) hb E C.1 C.2 Q hQC hQ hΔ φ hφker hφ C''.1 C''.2 hCC''

theorem law_beta_velu (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (C : CycSub E (N * ℓ)) (n : ℕ) (hn : ℓ = 2 * n + 1) (Q : E.toAffine.Point) (hQC : Q ∈ C.1)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (E.veluQuotient (E.oddOrderSummingSet Q n)).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : κ) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q n) x)
          (E.veluY (E.oddOrderSummingSet Q n) x y) h')
    (C'' : CycSub (E.veluQuotient (E.oddOrderSummingSet Q n)) N) (hCC'' : ∀ T ∈ C.1, φ T ∈ C''.1) :
    (fPl hNℓ E C.1).restrictAlong (heckeBetaC κ N ℓ) hβ =
      gPl hNℓ (E.veluQuotient (E.oddOrderSummingSet Q n)) C''.1 := by
  have hb : (betaMS κ N ℓ).toRingHom.IsIntegral :=
    isIntegral_of_comm (eC hNℓ) (eR hNℓ) (heckeBetaC κ N ℓ) (betaMS κ N ℓ) (heckeBetaC_eC hNℓ) hβ
  rw [fPl, gPl, restrictAlong_transport (eC hNℓ) (eR hNℓ) (heckeBetaC κ N ℓ) (betaMS κ N ℓ)
    (heckeBetaC_eC hNℓ) hβ hb]
  congr 1
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient κ N ℓ hNℓ
    (huniq_of N (hN_of hNℓ)) (hex_of (N * ℓ) hNℓ)
    (betaMS κ N ℓ) (fun f => rfl) hb E C.1 C.2 n hn Q hQC hQ hΔ φ hφker hφ C''.1 C''.2 hCC''

end Clauses

section VC

variable {κ : Type} [Field κ] [DecidableEq κ]

theorem heq_equivOfVariableChangeEq_symm (γ : VariableChange κ) (W : WeierstrassCurve.Affine κ)
    {V : WeierstrassCurve.Affine κ} (h : γ • W = V) (T : W.Point) :
    HEq ((Point.equivOfVariableChangeEq h).symm T) (Point.vcInvFun γ W T) := by
  subst h; rfl

theorem equivOfVariableChangeEq_symm_add (γ : VariableChange κ) (W : WeierstrassCurve.Affine κ)
    {V : WeierstrassCurve.Affine κ} (h : γ • W = V) (T₁ T₂ : W.Point) :
    (Point.equivOfVariableChangeEq h).symm (T₁ + T₂) =
      (Point.equivOfVariableChangeEq h).symm T₁ + (Point.equivOfVariableChangeEq h).symm T₂ := by
  subst h
  exact Point.vcInvFun_add γ W T₁ T₂

def vcMap {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') :
    E.toAffine.Point ≃+ E'.toAffine.Point :=
  AddEquiv.mk' (Point.equivOfVariableChangeEq (W := E.toAffine) (V := E'.toAffine) h).symm
    (equivOfVariableChangeEq_symm_add γ E.toAffine h)

theorem vcMap_apply {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') (T : E.toAffine.Point) :
    vcMap h T = (Point.equivOfVariableChangeEq (W := E.toAffine) (V := E'.toAffine) h).symm T := rfl

theorem heq_vcMap {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E') (T : E.toAffine.Point) :
    HEq (vcMap h T) (Point.vcInvFun γ E.toAffine T) :=
  heq_equivOfVariableChangeEq_symm γ E.toAffine h T

theorem forall_heq_iff {E E' : WeierstrassCurve κ} {γ : VariableChange κ} (h : γ • E = E')
    (A : Set E.toAffine.Point) (B : Set E'.toAffine.Point) :
    (∀ T ∈ A, ∃ T' ∈ B, HEq (Point.vcInvFun γ E.toAffine T) T') ↔ ∀ T ∈ A, vcMap h T ∈ B := by
  subst h
  constructor
  · intro H T hT
    obtain ⟨T', hT', hh⟩ := H T hT
    have : vcMap (rfl : γ • E = γ • E) T = T' := eq_of_heq ((heq_vcMap rfl T).trans hh)
    rw [this]; exact hT'
  · intro H T hT
    exact ⟨_, H T hT, (heq_vcMap rfl T).symm⟩

end VC

section Subgroups

variable {G : Type*} [AddCommGroup G]

theorem exists_zmultiples_eq (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ) (hn : Nat.card C = n) :
    ∃ P : G, AddSubgroup.zmultiples P = C ∧ addOrderOf P = n := by
  obtain ⟨P, hP⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨P, hP, ?_⟩
  rw [← Nat.card_zmultiples, hP, hn]

theorem nsmul_id_apply (n : ℕ) (T : G) : (n • AddMonoidHom.id G) T = n • T := rfl

theorem map_nsmul_zmultiples (n : ℕ) (P : G) :
    (AddSubgroup.zmultiples P).map (n • AddMonoidHom.id G) = AddSubgroup.zmultiples (n • P) := by
  rw [AddMonoidHom.map_zmultiples]; rfl

theorem mem_map_nsmul_iff (n : ℕ) (A : AddSubgroup G) (T : G) :
    T ∈ A.map (n • AddMonoidHom.id G) ↔ ∃ S ∈ A, n • S = T := by
  simp only [AddSubgroup.mem_map, nsmul_id_apply]

theorem map_nsmul_le (n : ℕ) (A : AddSubgroup G) : A.map (n • AddMonoidHom.id G) ≤ A := by
  rintro T ⟨S, hS, rfl⟩
  exact A.nsmul_mem hS n

theorem map_nsmul_map {H : Type*} [AddCommGroup H] (f : G →+ H) (n : ℕ) (A : AddSubgroup G) :
    (A.map (n • AddMonoidHom.id G)).map f = (A.map f).map (n • AddMonoidHom.id H) := by
  rw [AddSubgroup.map_map, AddSubgroup.map_map]
  congr 1
  ext T
  show f (n • T) = n • f T
  rw [map_nsmul]

theorem addOrderOf_nsmul_of_mul {P : G} {m n : ℕ} (hn : n ≠ 0) (h : addOrderOf P = m * n) :
    addOrderOf (n • P) = m := by
  rw [addOrderOf_nsmul' P hn, h, Nat.gcd_eq_right (dvd_mul_left n m), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)]

variable {N ℓ : ℕ}

theorem cyclic_map_nsmul_ell (hℓ : ℓ ≠ 0) (C : AddSubgroup G) (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) :
    IsAddCyclic (C.map (ℓ • AddMonoidHom.id G)) ∧ Nat.card (C.map (ℓ • AddMonoidHom.id G)) = N := by
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [map_nsmul_zmultiples]
  exact ⟨inferInstance, by rw [Nat.card_zmultiples, addOrderOf_nsmul_of_mul hℓ hP]⟩

theorem cyclic_map_nsmul_N (hN : N ≠ 0) (C : AddSubgroup G) (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) :
    IsAddCyclic (C.map (N • AddMonoidHom.id G)) ∧ Nat.card (C.map (N • AddMonoidHom.id G)) = ℓ := by
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [map_nsmul_zmultiples]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zmultiples, addOrderOf_nsmul_of_mul hN]
  rw [hP, Nat.mul_comm]

theorem cyclic_map_equiv {H : Type*} [AddCommGroup H] (e : G ≃+ H) (C : AddSubgroup G) (n : ℕ)
    (hC : IsAddCyclic C ∧ Nat.card C = n) :
    IsAddCyclic (C.map e.toAddMonoidHom) ∧ Nat.card (C.map e.toAddMonoidHom) = n := by
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  rw [AddMonoidHom.map_zmultiples]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zmultiples, ← hP]
  exact AddEquiv.addOrderOf_eq e P

theorem map_equiv_symm_map {H : Type*} [AddCommGroup H] (e : G ≃+ H) (C : AddSubgroup G) :
    (C.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = C := by
  rw [AddSubgroup.map_map]
  convert AddSubgroup.map_id C
  ext T
  exact e.symm_apply_apply T

theorem map_map_equiv_symm {H : Type*} [AddCommGroup H] (e : G ≃+ H) (C : AddSubgroup H) :
    (C.map e.symm.toAddMonoidHom).map e.toAddMonoidHom = C := by
  rw [AddSubgroup.map_map]
  convert AddSubgroup.map_id C
  ext T
  exact e.apply_symm_apply T

end Subgroups

section VeluData

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
  (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)

theorem exists_veluData (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral) (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0)
    (E : WeierstrassCurve κ) [E.IsElliptic] (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ) :
    ∃ (A : WeierstrassCurve κ) (_ : A.IsElliptic)
      (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point),
      φ ∈ rationalHomSet κ E A ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
          α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ) ∧
      ∀ (C : CycSub E (N * ℓ)), Q ∈ C.1 → ∀ C'' : CycSub A N, (∀ T ∈ C.1, φ T ∈ C''.1) →
        (fPl hNℓ E C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = gPl hNℓ A C''.1 := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hℓ.one_lt.ne hQ
  have hℓQ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hΔf : (E.fullKernelQuotient Q ℓ).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero ℓ E hℓ0 Q hQ
  rcases hℓ.eq_two_or_odd' with h2 | hodd
  ·
    subst h2
    rcases Q with _ | ⟨x₀, y₀, hns⟩
    · exact absurd rfl hQ0
    have hneg : -(Affine.Point.some x₀ y₀ hns) = Affine.Point.some x₀ y₀ hns := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, hℓQ]
    have hy₀ : E.toAffine.negY x₀ y₀ = y₀ := by
      rw [Affine.Point.neg_some] at hneg
      exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : E.veluGy x₀ y₀ = 0 := E.veluGy_eq_zero_of_negY_eq hy₀
    have hA2 : E.fullKernelQuotient (.some x₀ y₀ hns) 2 = E.veluQuotient2 x₀ y₀ := fullKernelQuotient_two E hns hgy
    have hΔ2 : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := hA2 ▸ hΔf
    haveI hA : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ2⟩
    obtain ⟨π₀, hπcoe, hπrat, -, hπuniv⟩ :=
      exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul hℓ0 E hns.1 hgy hΔ2
    let π : (E.baseChange κ).toAffine.Point →+ ((E.veluQuotient2 x₀ y₀).baseChange κ).toAffine.Point := π₀
    have hπapp : ∀ P : E.toAffine.Point, π P = veluPointMap2 hℓ0 hns.1 hgy hΔ2 P := fun P => by
      show π₀ P = _; rw [hπcoe]
    have hπQ : π (.some x₀ y₀ hns) = 0 := by
      rw [hπapp]; exact veluPointMap2_some_of_eq hℓ0 hns.1 hgy hΔ2 hns rfl
    have hπker : π.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := by
      refine le_antisymm ?_ ((AddSubgroup.zmultiples_le_of_mem) hπQ)
      intro P hP
      rw [AddMonoidHom.mem_ker] at hP
      rcases P with _ | ⟨x, y, h⟩
      · exact zero_mem _
      · by_cases hx : x = x₀
        · subst hx
          have hy : y = y₀ := by
            rcases eq_or_ne y (E.toAffine.negY x y₀) with h1 | h1
            · rw [h1, hy₀]
            · exact Affine.Y_eq_of_Y_ne h.1 hns.1 rfl h1
          subst hy
          exact AddSubgroup.mem_zmultiples _
        · exfalso
          rw [hπapp] at hP
          exact Affine.Point.some_ne_zero _ ((veluPointMap2_some_of_ne hℓ0 hns.1 hgy hΔ2 h hx).symm.trans hP)
    have hπker₀ : π₀.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := hπker
    refine ⟨E.veluQuotient2 x₀ y₀, hA, π, hπrat, hπker, fun V _ α hα hαQ => ?_, ?_⟩
    · refine hπuniv V inferInstance α hα fun T hT => ?_
      have hT' : T ∈ π.ker := hT
      rw [hπker] at hT'
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT'
      rw [map_zsmul]
      exact (congrArg (k • ·) hαQ).trans (smul_zero k)
    · intro C hQC C'' hCC''
      have law := fun (φ : E.toAffine.Point →+ (E.fullKernelQuotient (.some x₀ y₀ hns) 2).toAffine.Point) =>
        law_beta_full hNℓ hβ E C (.some x₀ y₀ hns) hQC hQ hΔf φ
      rw [hA2] at law
      exact law π₀ hπker₀ (fun P hP => by rw [hπcoe]; exact WeierstrassCurve.coordsOrZero_veluPointMap2 E hℓ0 hns hgy hΔ2 P hP)
        C'' hCC''
  ·
    have hℓ2 : ℓ ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hℓn : ℓ = 2 * (ℓ / 2) + 1 := (Nat.two_mul_div_two_add_one_of_odd hodd).symm
    have hQ' : addOrderOf Q = 2 * (ℓ / 2) + 1 := hQ.trans hℓn
    have hAv : E.fullKernelQuotient Q ℓ = E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)) := by
      have h := fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet E Q (ℓ / 2) hQ'
      rwa [← hℓn] at h
    have hΔv : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0 := hAv ▸ hΔf
    haveI hA : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔv⟩
    obtain ⟨φ₀, hker, hφ₀⟩ := exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hℓ hℓ2 hℓ0 Q hQ
    obtain ⟨hφrat, huniv⟩ :=
      veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq E (ℓ / 2) Q hQ' φ₀ hker hφ₀
    refine ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), hA, φ₀, hφrat, hker,
      fun V _ α hα hαQ => huniv V α hα hαQ, ?_⟩
    intro C hQC C'' hCC''
    exact law_beta_velu hNℓ hβ E C (ℓ / 2) hℓn Q hQC hQ' hΔv φ₀ hker hφ₀ C'' hCC''

end VeluData

section Image

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {N ℓ : ℕ}

theorem cyclic_map_of_ker (hN : N ≠ 0) (hℓ : ℓ ≠ 0) (φ : G →+ H) (C : AddSubgroup G)
    (hC : IsAddCyclic C ∧ Nat.card C = N * ℓ) (hker : φ.ker = C.map (N • AddMonoidHom.id G)) :
    IsAddCyclic (C.map φ) ∧ Nat.card (C.map φ) = N := by
  obtain ⟨P, hPC, hP⟩ := exists_zmultiples_eq C hC.1 _ hC.2
  have hmap : C.map φ = AddSubgroup.zmultiples (φ P) := by rw [← hPC, AddMonoidHom.map_zmultiples]
  rw [hmap]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zmultiples]
  have hkerP : φ.ker = AddSubgroup.zmultiples (N • P) := by rw [hker, ← hPC, map_nsmul_zmultiples]
  apply Nat.dvd_antisymm
  ·
    apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← AddMonoidHom.mem_ker, hkerP]
    exact AddSubgroup.mem_zmultiples _
  ·
    set n := addOrderOf (φ P) with hn
    have h1 : n • P ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_nsmul]; exact addOrderOf_nsmul_eq_zero (φ P)
    rw [hkerP] at h1
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h1

    have h2 : ((n : ℤ) - m * N) • P = 0 := by
      rw [sub_smul, mul_smul, natCast_zsmul, natCast_zsmul, hm]; abel
    have h3 : ((N * ℓ : ℕ) : ℤ) ∣ (n : ℤ) - m * N := by
      rw [← hP]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2
    have h4 : (N : ℤ) ∣ (n : ℤ) - m * N := (Int.natCast_dvd_natCast.mpr (dvd_mul_right N ℓ)).trans h3
    have h5 : (N : ℤ) ∣ (n : ℤ) := by
      have := h4.add (dvd_mul_left (N : ℤ) m)
      rwa [sub_add_cancel] at this
    exact_mod_cast h5

end Image

section Count

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0) (hℓ : ℓ.Prime)
  (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
  (E_a : WeierstrassCurve κ) [E_a.IsElliptic]
  (C_a : AddSubgroup E_a.toAffine.Point) (hCa : IsAddCyclic C_a ∧ Nat.card C_a = N)
  (a : Place κ (modularFunctionFieldC κ N)) (hga : gPl hNℓ E_a C_a = a)

def ellPart (C : CycSub E_a (N * ℓ)) : CycSub E_a N :=
  ⟨C.1.map (ℓ • AddMonoidHom.id _), cyclic_map_nsmul_ell (NeZero.ne ℓ) C.1 C.2⟩

theorem ellPart_val (C : CycSub E_a (N * ℓ)) : (ellPart E_a C).1 = C.1.map (ℓ • AddMonoidHom.id _) := rfl

def ma : ℕ := Nat.card {C' : CycSub E_a N // gPl hNℓ E_a C'.1 = gPl hNℓ E_a C_a}

include hCa in
theorem ord_a_eq : (gPl hNℓ E_a C_a).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E_a.j) =
    (ma hNℓ E_a C_a : ℤ) :=
  g4 hNℓ E_a ⟨C_a, hCa⟩

include hCa in
theorem ma_pos : 0 < ma hNℓ E_a C_a := by
  have h := g1 hNℓ E_a ⟨C_a, hCa⟩
  have h' := ord_a_eq hNℓ E_a C_a hCa
  simp only at h
  omega

theorem restrictAlong_alpha (C : CycSub E_a (N * ℓ)) :
    (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = gPl hNℓ E_a (ellPart E_a C).1 :=
  law_alpha hNℓ hα E_a C (ellPart E_a C) (fun T hT => ⟨T, hT, rfl⟩)

theorem ord_alpha_sub (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    W.ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E_a.j) =
      W.ramificationIndexAlong (heckeAlphaC κ N ℓ) *
        (W.restrictAlong (heckeAlphaC κ N ℓ) hα).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E_a.j) := by
  rw [← Place.ord_restrictAlong, map_sub, AlgHom.commutes]

include hCa hga in

theorem exists_of_restrictAlong_eq (W : Place κ (charLDegeneracyRoof κ N ℓ))
    (hW : W.restrictAlong (heckeAlphaC κ N ℓ) hα = a) : ∃ C : CycSub E_a (N * ℓ), fPl hNℓ E_a C.1 = W := by
  apply f2 hNℓ E_a W
  rw [ord_alpha_sub hα E_a W, hW, ← hga, ord_a_eq hNℓ E_a C_a hCa]
  have h1 := ramificationIndexAlong_pos (heckeAlphaC κ N ℓ) hα W
  have h2 := ma_pos hNℓ E_a C_a hCa
  positivity

include hCa hga in

theorem natCard_fibre_eq (C : CycSub E_a (N * ℓ)) (hC : (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = a) :
    (Nat.card {C' : CycSub E_a (N * ℓ) // fPl hNℓ E_a C'.1 = fPl hNℓ E_a C.1} : ℤ) =
      (fPl hNℓ E_a C.1).ramificationIndexAlong (heckeAlphaC κ N ℓ) * ma hNℓ E_a C_a := by
  rw [← f4 hNℓ E_a C, ord_alpha_sub hα E_a, hC, ← hga, ord_a_eq hNℓ E_a C_a hCa]

theorem fPl_map_vcMap {γ : VariableChange κ} (hγ : γ • E_a = E_a) (A : CycSub E_a (N * ℓ)) :
    fPl hNℓ E_a (A.1.map (vcMap hγ).toAddMonoidHom) = fPl hNℓ E_a A.1 := by
  have hA' := cyclic_map_equiv (vcMap hγ) A.1 (N * ℓ) A.2
  symm
  exact (f3 hNℓ E_a A ⟨_, hA'⟩).mpr ⟨γ, hγ, (forall_heq_iff hγ A.1 _).mpr fun T hT => ⟨T, hT, rfl⟩⟩

theorem fPl_map_vcMap_symm {γ : VariableChange κ} (hγ : γ • E_a = E_a) (A : CycSub E_a (N * ℓ)) :
    fPl hNℓ E_a (A.1.map (vcMap hγ).symm.toAddMonoidHom) = fPl hNℓ E_a A.1 := by
  have hA' := cyclic_map_equiv (vcMap hγ).symm A.1 (N * ℓ) A.2
  have h := fPl_map_vcMap hNℓ E_a hγ ⟨_, hA'⟩
  rw [← h]
  simp only [map_map_equiv_symm]

include hCa hga in

theorem natCard_orbit (b : Place κ (modularFunctionFieldC κ N)) :
    Nat.card {C : CycSub E_a (N * ℓ) //
        (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = a ∧
          (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} =
      ma hNℓ E_a C_a * Nat.card {C : CycSub E_a (N * ℓ) //
        C.1.map (ℓ • AddMonoidHom.id _) = C_a ∧ (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} := by
  classical
  let Φ := {C' : CycSub E_a N // gPl hNℓ E_a C'.1 = gPl hNℓ E_a C_a}
  let SC : AddSubgroup E_a.toAffine.Point → Type := fun B => {C : CycSub E_a (N * ℓ) //
    C.1.map (ℓ • AddMonoidHom.id _) = B ∧ (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b}

  have e1 : {C : CycSub E_a (N * ℓ) //
        (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = a ∧
          (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} ≃ Σ C' : Φ, SC C'.1.1 :=
    { toFun := fun C => ⟨⟨ellPart E_a C.1, by rw [← restrictAlong_alpha hNℓ hα E_a C.1, C.2.1, hga]⟩, C.1, rfl, C.2.2⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 : (ellPart E_a p.2.1).1 = p.1.1.1 := p.2.2.1
          have h2 : gPl hNℓ E_a (ellPart E_a p.2.1).1 = gPl hNℓ E_a C_a := by rw [h1]; exact p.1.2
          rw [restrictAlong_alpha hNℓ hα E_a, h2, hga], p.2.2.2⟩
      left_inv := fun C => rfl
      right_inv := fun p => by
        refine Sigma.subtype_ext (Subtype.ext (Subtype.ext p.2.2.1)) rfl }

  have e2 : ∀ C' : Φ, Nonempty (SC C'.1.1 ≃ SC C_a) := by
    rintro ⟨C', hC'⟩
    obtain ⟨γ, hγ, hmap⟩ := (g3 hNℓ E_a E_a C' ⟨C_a, hCa⟩).mp hC'
    replace hmap := (forall_heq_iff hγ (C'.1 : Set _) (C_a : Set _)).mp hmap
    let θ : E_a.toAffine.Point ≃+ E_a.toAffine.Point := vcMap hγ
    have hθC' : C'.1.map θ.toAddMonoidHom = C_a := by
      haveI : Finite C_a := Nat.finite_of_card_ne_zero (by rw [hCa.2]; exact NeZero.ne N)
      apply AddSubgroup.eq_of_le_of_card_ge
      · rintro T ⟨S, hS, rfl⟩; exact hmap S hS
      · rw [hCa.2, (cyclic_map_equiv θ C'.1 N C'.2).2]
    have hθC'symm : C_a.map θ.symm.toAddMonoidHom = C'.1 := by
      rw [← hθC', map_equiv_symm_map]
    refine ⟨{ toFun := fun C => ⟨⟨C.1.1.map θ.toAddMonoidHom, cyclic_map_equiv θ C.1.1 _ C.1.2⟩, ?_, ?_⟩
              invFun := fun C => ⟨⟨C.1.1.map θ.symm.toAddMonoidHom, cyclic_map_equiv θ.symm C.1.1 _ C.1.2⟩, ?_, ?_⟩
              left_inv := fun C => Subtype.ext (Subtype.ext (map_equiv_symm_map θ C.1.1))
              right_inv := fun C => Subtype.ext (Subtype.ext (map_map_equiv_symm θ C.1.1)) }⟩
    · show (C.1.1.map θ.toAddMonoidHom).map (ℓ • AddMonoidHom.id _) = C_a
      rw [← map_nsmul_map, C.2.1, hθC']
    · show (fPl hNℓ E_a (C.1.1.map (vcMap hγ).toAddMonoidHom)).restrictAlong (heckeBetaC κ N ℓ) hβ = b
      rw [fPl_map_vcMap hNℓ E_a hγ C.1]; exact C.2.2
    · show (C.1.1.map θ.symm.toAddMonoidHom).map (ℓ • AddMonoidHom.id _) = C'.1
      rw [← map_nsmul_map, C.2.1, hθC'symm]
    · show (fPl hNℓ E_a (C.1.1.map (vcMap hγ).symm.toAddMonoidHom)).restrictAlong (heckeBetaC κ N ℓ) hβ = b
      rw [fPl_map_vcMap_symm hNℓ E_a hγ C.1]; exact C.2.2

  have e3 : (Σ C' : Φ, SC C'.1.1) ≃ Φ × SC C_a :=
    (Equiv.sigmaCongrRight fun C' => (e2 C').some).trans (Equiv.sigmaEquivProd Φ (SC C_a))
  rw [Nat.card_congr (e1.trans e3), Nat.card_prod]
  rfl

include hℓ in

theorem key_iff (hℓq0 : (ℓ : κ) ≠ 0) (E_b : WeierstrassCurve κ) [E_b.IsElliptic]
    (C_b : AddSubgroup E_b.toAffine.Point) (hCb : IsAddCyclic C_b ∧ Nat.card C_b = N)
    (b : Place κ (modularFunctionFieldC κ N)) (hgb : gPl hNℓ E_b C_b = b)
    (C : CycSub E_a (N * ℓ)) :
    (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b ↔
      ∃ ψ' ∈ rationalHomSet κ E_a E_b, ∃ ψ ∈ rationalHomSet κ E_b E_a,
        ψ'.ker = C.1.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C.1, ψ' T ∈ C_b := by

  obtain ⟨hDc, hDcard⟩ := cyclic_map_nsmul_N (NeZero.ne N) C.1 C.2 (ℓ := ℓ)
  obtain ⟨Q, hQD, hQ⟩ := exists_zmultiples_eq _ hDc ℓ hDcard
  have hQC : Q ∈ C.1 := map_nsmul_le N C.1 (hQD ▸ AddSubgroup.mem_zmultiples Q)

  obtain ⟨A, hA, φ, hφ, hker, huniv, hlaw⟩ := exists_veluData hNℓ hβ hℓ hℓq0 E_a Q hQ
  let φ' : E_a.toAffine.Point →+ A.toAffine.Point := φ
  have hφ'ker : φ'.ker = C.1.map (N • AddMonoidHom.id _) := hker.trans hQD

  let C'' : CycSub A N := ⟨C.1.map φ', cyclic_map_of_ker (NeZero.ne N) (NeZero.ne ℓ) φ' C.1 C.2 hφ'ker⟩
  have hCC'' : ∀ T ∈ C.1, φ' T ∈ C''.1 := fun T hT => ⟨T, hT, rfl⟩

  rw [hlaw C hQC C'' hCC'', ← hgb, g3 hNℓ A E_b C'' ⟨C_b, hCb⟩]

  have hre : ∀ γ : VariableChange κ,
      (∀ T ∈ C''.1, ∃ T' ∈ C_b, HEq (Point.vcInvFun γ A.toAffine T) T') ↔
        ∀ S ∈ (C.1 : Set E_a.toAffine.Point), ∃ T' ∈ (C_b : Set E_b.toAffine.Point),
          HEq (Point.vcInvFun γ A.toAffine (φ S)) T' := by
    intro γ
    constructor
    · intro H S hS
      exact H (φ' S) ⟨S, hS, rfl⟩
    · rintro H T ⟨S, hS, rfl⟩
      exact H S hS
  simp only [hre]
  rw [WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair E_a A E_b hℓ hℓq0 Q hQ φ hφ hker huniv
    (C.1 : Set _) (C_b : Set _), hQD]
  exact Iff.rfl

include hℓ in

theorem natCard_levelStructures_eq (hℓq0 : (ℓ : κ) ≠ 0) (E_b : WeierstrassCurve κ) [E_b.IsElliptic]
    (C_b : AddSubgroup E_b.toAffine.Point) (hCb : IsAddCyclic C_b ∧ Nat.card C_b = N)
    (b : Place κ (modularFunctionFieldC κ N)) (hgb : gPl hNℓ E_b C_b = b) :
    Nat.card {C : CycSub E_a (N * ℓ) //
        C.1.map (ℓ • AddMonoidHom.id _) = C_a ∧ (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} =
      Nat.card {Cp : AddSubgroup E_a.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C_a ∧
        ∃ ψ' ∈ rationalHomSet κ E_a E_b, ∃ ψ ∈ rationalHomSet κ E_b E_a,
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C_b} := by
  have key := key_iff hNℓ hℓ hβ E_a hℓq0 E_b C_b hCb b hgb
  exact Nat.card_congr
    { toFun := fun C => ⟨C.1.1, C.1.2, C.2.1, (key C.1).mp C.2.2⟩
      invFun := fun D => ⟨⟨D.1, D.2.1⟩, D.2.2.1, (key ⟨D.1, D.2.1⟩).mpr D.2.2.2⟩
      left_inv := fun C => rfl
      right_inv := fun D => rfl }

set_option maxHeartbeats 6400000 in
include hℓ hCa hga in
open Classical in

theorem finsum_eq_natCard [Fact ℓ.Prime] (hℓq0 : (ℓ : κ) ≠ 0) (E_b : WeierstrassCurve κ) [E_b.IsElliptic]
    (C_b : AddSubgroup E_b.toAffine.Point) (hCb : IsAddCyclic C_b ∧ Nat.card C_b = N)
    (b : Place κ (modularFunctionFieldC κ N)) (hgb : gPl hNℓ E_b C_b = b) :
    (∑ᶠ W : Place κ (charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeBetaC κ N ℓ) hβ = b ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = a then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      (Nat.card {Cp : AddSubgroup E_a.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C_a ∧
        ∃ ψ' ∈ rationalHomSet κ E_a E_b, ∃ ψ ∈ rationalHomSet κ E_b E_a,
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C_b} : ℤ) := by
  classical
  haveI : HasPrincipalDivisors κ (charLDegeneracyRoof κ N ℓ) :=
    hasPrincipalDivisors_charLDegeneracyRoof κ N ℓ (hN_of hNℓ) hℓq0

  set T : Finset (Place κ (charLDegeneracyRoof κ N ℓ)) := Place.fiberAlong (heckeAlphaC κ N ℓ) hα a with hT
  have hmemT : ∀ W, W ∈ T ↔ W.restrictAlong (heckeAlphaC κ N ℓ) hα = a := fun W => Place.mem_fiberAlong
  have hfibfin : ∀ W : Place κ (charLDegeneracyRoof κ N ℓ), W.restrictAlong (heckeAlphaC κ N ℓ) hα = a →
      Finite {C' : CycSub E_a (N * ℓ) // fPl hNℓ E_a C'.1 = W} := by
    intro W hW
    obtain ⟨C, rfl⟩ := exists_of_restrictAlong_eq hNℓ hα E_a C_a hCa a hga W hW
    apply Nat.finite_of_card_ne_zero
    have h1 := natCard_fibre_eq hNℓ hα E_a C_a hCa a hga C hW
    have h2 := ramificationIndexAlong_pos (heckeAlphaC κ N ℓ) hα (fPl hNℓ E_a C.1)
    have h3 := ma_pos hNℓ E_a C_a hCa
    intro h0
    rw [h0, Nat.cast_zero] at h1
    have : (0 : ℤ) < (fPl hNℓ E_a C.1).ramificationIndexAlong (heckeAlphaC κ N ℓ) * ma hNℓ E_a C_a := by positivity
    omega

  rw [finsum_eq_sum_of_support_subset _ (s := T) (by
    intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, hmemT]
    by_contra ha'
    exact hW (if_neg fun h => ha' h.2))]
  set T' := T.filter (fun W => W.restrictAlong (heckeBetaC κ N ℓ) hβ = b) with hT'
  have hLHS : (∑ W ∈ T, if W.restrictAlong (heckeBetaC κ N ℓ) hβ = b ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = a then
        (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      ∑ W ∈ T', (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hWa := (hmemT W).mp hW
    by_cases hWb : W.restrictAlong (heckeBetaC κ N ℓ) hβ = b
    · rw [if_pos ⟨hWb, hWa⟩, if_pos hWb]
    · rw [if_neg fun h => hWb h.1, if_neg hWb]
  rw [hLHS]

  have hmemT' : ∀ W, W ∈ T' → W.restrictAlong (heckeAlphaC κ N ℓ) hα = a ∧ W.restrictAlong (heckeBetaC κ N ℓ) hβ = b :=
    fun W hW => ⟨(hmemT W).mp (Finset.mem_filter.mp hW).1, (Finset.mem_filter.mp hW).2⟩
  haveI : ∀ W : T', Finite {C' : CycSub E_a (N * ℓ) // fPl hNℓ E_a C'.1 = W.1} :=
    fun W => hfibfin W.1 (hmemT' W.1 W.2).1
  have hS : (ma hNℓ E_a C_a : ℤ) * ∑ W ∈ T', (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) =
      Nat.card {C : CycSub E_a (N * ℓ) //
        (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = a ∧
          (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} := by
    have hsigma : Nat.card {C : CycSub E_a (N * ℓ) //
        (fPl hNℓ E_a C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = a ∧
          (fPl hNℓ E_a C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = b} =
        Nat.card (Σ W : T', {C' : CycSub E_a (N * ℓ) // fPl hNℓ E_a C'.1 = W.1}) := by
      refine Nat.card_congr
        { toFun := fun C => ⟨⟨fPl hNℓ E_a C.1.1, Finset.mem_filter.mpr ⟨(hmemT _).mpr C.2.1, C.2.2⟩⟩, C.1, rfl⟩
          invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact hmemT' p.1.1 p.1.2⟩
          left_inv := fun C => rfl
          right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2) rfl }
    rw [hsigma, Nat.card_sigma, Finset.sum_coe_sort T' (fun W => Nat.card {C' : CycSub E_a (N * ℓ) // fPl hNℓ E_a C'.1 = W}),
      Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨C, rfl⟩ := exists_of_restrictAlong_eq hNℓ hα E_a C_a hCa a hga W (hmemT' W hW).1
    rw [natCard_fibre_eq hNℓ hα E_a C_a hCa a hga C (hmemT' _ hW).1, mul_comm]

  have horbit := natCard_orbit hNℓ hα hβ E_a C_a hCa a hga b
  have hlevel := natCard_levelStructures_eq hNℓ hℓ hβ E_a C_a hℓq0 E_b C_b hCb b hgb
  rw [horbit, hlevel, Nat.cast_mul] at hS
  have hma : (ma hNℓ E_a C_a : ℤ) ≠ 0 := by exact_mod_cast (ma_pos hNℓ E_a C_a hCa).ne'
  exact mul_left_cancel₀ hma hS

end Count

end ModularCurve.TransposeRoofCount
p2m_reactivate "P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve.TransposeRoofCount"
p2m_reactivate "P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve"

open ModularCurve.TransposeRoofCount in
open Classical in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : Place κ ↥(modularFunctionFieldC κ N))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (C_x : AddSubgroup E_x.toAffine.Point) (C_y : AddSubgroup E_y.toAffine.Point)
    (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (hx : x.toValuationSubring = (moduliPlace κ N E_x C_x).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom)
    (hy : y.toValuationSubring = (moduliPlace κ N E_y C_y).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    (∑ᶠ W : Place κ ↥(charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeBetaC κ N ℓ) hβ = x ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = y then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      (Nat.card {Cp : AddSubgroup E_y.toAffine.Point //
        (IsAddCyclic Cp ∧ Nat.card Cp = N * ℓ) ∧ Cp.map (ℓ • AddMonoidHom.id _) = C_y ∧
        ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x, ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y,
          ψ'.ker = Cp.map (N • AddMonoidHom.id _) ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ Cp, ψ' T ∈ C_x} : ℤ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : κ) ≠ 0 := cast_ne_zero_of_cast_mul_ne_zero' hNℓ
  have hgx : gPl hNℓ E_x C_x = x := ((transport_eC_eq_iff hNℓ (moduliPlace κ N E_x C_x) x).mpr hx).symm
  have hgy : gPl hNℓ E_y C_y = y := ((transport_eC_eq_iff hNℓ (moduliPlace κ N E_y C_y) y).mpr hy).symm
  exact finsum_eq_natCard hNℓ hℓ hα hβ E_y C_y hCy y hgy hℓ0 E_x C_x hCx x hgx

end
p2m_reactivate "P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace.ModularCurve.TransposeRoofCount"

end S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
end P2MW
export P2MW.S_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace (solution)
