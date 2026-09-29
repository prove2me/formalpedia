-- Prove2me | solution 1 for ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/80c073bc-76cb-57d1-b098-5b40ea9cb3f3

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
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
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

namespace P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
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

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ssHeckeMatrixC charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC algebraMap_laurentSeries_apply_eq_single mem_restrictAlong_iff jqModC modularFunctionFieldC qExpand qExpand_single qExpand_congr qExpand_qExpand ssPlaces jGeomGen coe_jGeomGen ModuliPoint IsModuliPlaceOf moduliPlace divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full modularFunctionFieldC_le_full full_degeneracyC_le full_degeneracyC_map_le moduliPlace_orbitClauses moduliPlace_restrictAlong_inclusion moduliPlace_restrictAlong_qExpand_fullKernelQuotient moduliPlace_restrictAlong_qExpand_veluQuotient isModuliPlaceOf_nonempty eq_of_isModuliPlaceOf modularFunctionFieldC_eq_modularFunctionFieldFullC charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd inertiaDegAlong_heckeAlphaC_eq_one hasPrincipalDivisors_charLDegeneracyRoof"
namespace RoofCountLevelN
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

def autPlace (σ : Z ≃ₐ[K] Z) : Place K Z ≃ Place K Z :=
  Place.congrEquiv σ.toRingEquiv (fun a => σ.commutes a)

theorem mem_autPlace_iff (σ : Z ≃ₐ[K] Z) (W : Place K Z) (z : Z) :
    z ∈ (autPlace σ W).toValuationSubring ↔ σ.symm z ∈ W.toValuationSubring :=
  Iff.rfl

theorem ord_autPlace (σ : Z ≃ₐ[K] Z) (W : Place K Z) (z : Z) : (autPlace σ W).ord (σ z) = W.ord z :=
  Place.ord_congrRingEquiv σ.toRingEquiv (fun a => σ.commutes a) W z

theorem restrictAlong_autPlace (σ : Z ≃ₐ[K] Z) {φ ψ : F →ₐ[K] Z} (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (h : ∀ f, σ (ψ f) = φ f) (W : Place K Z) :
    (autPlace σ W).restrictAlong φ hφ = W.restrictAlong ψ hψ := by
  ext f
  show φ f ∈ (autPlace σ W).toValuationSubring ↔ ψ f ∈ W.toValuationSubring
  rw [mem_autPlace_iff, ← h, AlgEquiv.symm_apply_apply]

theorem ramificationIndexAlong_autPlace (σ : Z ≃ₐ[K] Z) {φ ψ : F →ₐ[K] Z} (h : ∀ f, σ (ψ f) = φ f)
    (W : Place K Z) : (autPlace σ W).ramificationIndexAlong φ = W.ramificationIndexAlong ψ := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (autPlace σ W).ord (φ f) = n} =
    sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (ψ f) = n}
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => exists_congr fun f => and_congr_right fun _ => ?_
  rw [← h f, ord_autPlace]

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

section Swap

variable (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem exists_swap_full (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hNℓ : ((N * ℓ : ℕ) : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K (N * ℓ) ≃ₐ[K] modularFunctionFieldFullC K (N * ℓ),
      (∀ f, σ (inclMS K N ℓ f) = betaMS K N ℓ f) ∧ (∀ f, σ (betaMS K N ℓ f) = inclMS K N ℓ f) := by
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd K N ℓ hℓ hℓN
    (cast_ne_zero_of_cast_mul_ne_zero hNℓ) (cast_ne_zero_of_cast_mul_ne_zero' hNℓ)
  have hext : ∀ (φ₁ φ₂ : modularFunctionFieldFullC K N →ₐ[K] modularFunctionFieldFullC K (N * ℓ)),
      (∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
        φ₁ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ = φ₂ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩) →
      φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    refine IntermediateField.algHom_ext_of_eq_adjoin K (S := modularFunctionFieldFullC K N)
      (s := divisorExpansionsC K N) rfl fun x hx => ?_
    obtain ⟨d, hd0, hd, rfl⟩ := hx
    exact h d hd0 hd
  refine ⟨σ, fun f => ?_, fun f => ?_⟩
  · refine AlgHom.congr_fun (hext (σ.toAlgHom.comp (inclMS K N ℓ)) (betaMS K N ℓ) fun d hd0 hd => ?_) f
    haveI := hd0
    have e1 : inclMS K N ℓ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
        ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * ℓ) (Dvd.dvd.mul_right hd ℓ)⟩ := Subtype.ext rfl
    show σ (inclMS K N ℓ _) = _
    rw [e1, (hσ d hd0 hd).1]
    apply Subtype.ext
    rw [coe_betaMS]
    show qExpand K (d * ℓ) (jqModC K) = qExpand K ℓ (qExpand K d (jqModC K))
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm d ℓ) _
  · refine AlgHom.congr_fun (hext (σ.toAlgHom.comp (betaMS K N ℓ)) (inclMS K N ℓ) fun d hd0 hd => ?_) f
    haveI := hd0
    have e1 : betaMS K N ℓ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
        ⟨qExpand K (d * ℓ) (jqModC K), jqModCd_mem_full K (N * ℓ) (Nat.mul_dvd_mul_right hd ℓ)⟩ := by
      apply Subtype.ext
      rw [coe_betaMS]
      show qExpand K ℓ (qExpand K d (jqModC K)) = qExpand K (d * ℓ) (jqModC K)
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm ℓ d) _
    show σ (betaMS K N ℓ _) = _
    rw [e1, (hσ d hd0 hd).2]
    exact Subtype.ext rfl

theorem exists_swap (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hNℓ : ((N * ℓ : ℕ) : K) ≠ 0) :
    ∃ σ : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ,
      (∀ f, σ (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) ∧
      (∀ f, σ (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f) := by
  obtain ⟨σ₀, h1, h2⟩ := exists_swap_full K N ℓ hℓ hℓN hNℓ
  refine ⟨((eR hNℓ).symm.trans σ₀).trans (eR hNℓ), fun f => ?_, fun f => ?_⟩
  · have hf : f = eC hNℓ ((eC hNℓ).symm f) := ((eC hNℓ).apply_symm_apply f).symm
    rw [hf, heckeAlphaC_eC, heckeBetaC_eC]
    show eR hNℓ (σ₀ ((eR hNℓ).symm (eR hNℓ (inclMS K N ℓ ((eC hNℓ).symm f))))) = _
    rw [AlgEquiv.symm_apply_apply, h1]
  · have hf : f = eC hNℓ ((eC hNℓ).symm f) := ((eC hNℓ).apply_symm_apply f).symm
    rw [hf, heckeBetaC_eC, heckeAlphaC_eC]
    show eR hNℓ (σ₀ ((eR hNℓ).symm (eR hNℓ (betaMS K N ℓ ((eC hNℓ).symm f))))) = _
    rw [AlgEquiv.symm_apply_apply, h2]

end Swap

section Entry

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (q' : ℕ) (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

open Classical in

theorem entry_eq_finsum (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' N κ)) :
    ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      ∑ᶠ W : Place κ (charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeAlphaC κ N ℓ) hα = x.1 ∧ W.restrictAlong (heckeBetaC κ N ℓ) hβ = y.1 then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0 := by
  obtain ⟨σ, hσα, hσβ⟩ := exists_swap κ N ℓ hℓ hℓN hNℓ
  rw [ssHeckeMatrixC, Matrix.of_apply, ← finsum_comp_equiv (autPlace σ)]
  refine finsum_congr fun W => ?_
  rw [restrictAlong_autPlace σ hβ hα hσα W, restrictAlong_autPlace σ hα hβ hσβ W,
    ramificationIndexAlong_autPlace σ hσα W, inertiaDegAlong_heckeAlphaC_eq_one κ N ℓ hα, Nat.cast_one, mul_one]

end Entry

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

theorem exists_bezout (hcop : N.Coprime ℓ) : ∃ u v : ℤ, ∀ T : G, T = u • ((ℓ : ℤ) • T) + v • ((N : ℤ) • T) := by
  refine ⟨N.gcdB ℓ, N.gcdA ℓ, fun T => ?_⟩
  have h : (1 : ℤ) = (N : ℤ) * N.gcdA ℓ + (ℓ : ℤ) * N.gcdB ℓ := by
    rw [← Nat.gcd_eq_gcd_ab N ℓ, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
  calc T = (1 : ℤ) • T := (one_zsmul T).symm
    _ = ((N : ℤ) * N.gcdA ℓ + (ℓ : ℤ) * N.gcdB ℓ) • T := by rw [← h]
    _ = _ := by rw [add_zsmul, mul_comm (N : ℤ), mul_comm (ℓ : ℤ), mul_zsmul, mul_zsmul, add_comm]

theorem map_ell_sup_map_N (hcop : N.Coprime ℓ) (C : AddSubgroup G) :
    C.map (ℓ • AddMonoidHom.id G) ⊔ C.map (N • AddMonoidHom.id G) = C := by
  refine le_antisymm (sup_le (map_nsmul_le ℓ C) (map_nsmul_le N C)) fun T hT => ?_
  obtain ⟨u, v, huv⟩ := exists_bezout (G := G) hcop
  rw [huv T]
  refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (AddSubgroup.zsmul_mem _ ?_ u))
    (AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem _ ?_ v))
  · exact ⟨T, hT, (natCast_zsmul T ℓ).symm⟩
  · exact ⟨T, hT, (natCast_zsmul T N).symm⟩

theorem exists_add_of_mem (hcop : N.Coprime ℓ) (C : AddSubgroup G) {T : G} (hT : T ∈ C) :
    ∃ a ∈ C.map (ℓ • AddMonoidHom.id G), ∃ d ∈ C.map (N • AddMonoidHom.id G), T = a + d := by
  have h : T ∈ C.map (ℓ • AddMonoidHom.id G) ⊔ C.map (N • AddMonoidHom.id G) := by
    rw [map_ell_sup_map_N hcop]; exact hT
  obtain ⟨a, ha, d, hd, rfl⟩ := AddSubgroup.mem_sup.mp h
  exact ⟨a, ha, d, hd, rfl⟩

theorem map_nsmul_eq_self_of_coprime {n m : ℕ} (A : AddSubgroup G) [Finite A] (hA : Nat.card A = m)
    (hcop : n.Coprime m) : A.map (n • AddMonoidHom.id G) = A := by
  apply AddSubgroup.eq_of_le_of_card_ge (map_nsmul_le n A)

  have hinj : Set.InjOn (fun T : G => n • T) A := by
    intro T₁ h₁ T₂ h₂ h12
    have h0 : n • (T₁ - T₂) = 0 := by rw [nsmul_sub]; exact sub_eq_zero.mpr h12
    have hmem : T₁ - T₂ ∈ A := A.sub_mem h₁ h₂
    have hdvd1 : addOrderOf (⟨T₁ - T₂, hmem⟩ : A) ∣ n := by
      apply addOrderOf_dvd_of_nsmul_eq_zero
      exact Subtype.ext h0
    have hdvd2 : addOrderOf (⟨T₁ - T₂, hmem⟩ : A) ∣ m := hA ▸ addOrderOf_dvd_natCard _
    have h1 : addOrderOf (⟨T₁ - T₂, hmem⟩ : A) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have := AddMonoid.addOrderOf_eq_one_iff.mp h1
    exact sub_eq_zero.mp (congrArg Subtype.val this)
  have hcard : Nat.card (A.map (n • AddMonoidHom.id G)) = Nat.card A := by
    have hset : ((A.map (n • AddMonoidHom.id G) : AddSubgroup G) : Set G) = (fun T : G => n • T) '' (A : Set G) := by
      ext T; simp only [SetLike.mem_coe, mem_map_nsmul_iff, Set.mem_image]
    have := Nat.card_image_of_injOn hinj
    rw [← hset] at this
    exact this
  exact le_of_eq hcard.symm

theorem map_nsmul_card_eq_bot {m : ℕ} (A : AddSubgroup G) [Finite A] (hA : Nat.card A = m) :
    A.map (m • AddMonoidHom.id G) = ⊥ := by
  rw [eq_bot_iff]
  rintro T ⟨S, hS, rfl⟩
  rw [AddSubgroup.mem_bot, nsmul_id_apply, ← hA]
  have h := card_nsmul_eq_zero' (x := (⟨S, hS⟩ : A))
  exact congrArg Subtype.val h

theorem cyclic_sup (hℓ : ℓ.Prime) (hcop : N.Coprime ℓ) (A D : AddSubgroup G)
    (hA : IsAddCyclic A ∧ Nat.card A = N) (hD : Nat.card D = ℓ) :
    IsAddCyclic ↥(A ⊔ D) ∧ Nat.card ↥(A ⊔ D) = N * ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hDc : IsAddCyclic D := isAddCyclic_of_prime_card hD
  obtain ⟨P, rfl, hP⟩ := exists_zmultiples_eq A hA.1 _ hA.2
  obtain ⟨Q, rfl, hQ⟩ := exists_zmultiples_eq D hDc _ hD
  have hord : addOrderOf (P + Q) = N * ℓ := by
    rw [← hP, ← hQ]
    exact (AddCommute.all P Q).addOrderOf_add_eq_mul_addOrderOf_of_coprime (by rwa [hP, hQ])
  have heq : AddSubgroup.zmultiples P ⊔ AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (P + Q) := by
    apply le_antisymm
    · obtain ⟨u, v, huv⟩ := exists_bezout (G := G) hcop
      have hℓQ : (ℓ : ℤ) • Q = 0 := by rw [natCast_zsmul, ← hQ]; exact addOrderOf_nsmul_eq_zero Q
      have hNP : (N : ℤ) • P = 0 := by rw [natCast_zsmul, ← hP]; exact addOrderOf_nsmul_eq_zero P
      refine sup_le ?_ ?_
      · rw [AddSubgroup.zmultiples_le]
        have h1 : u • ((ℓ : ℤ) • (P + Q)) = P := by
          rw [zsmul_add, hℓQ, add_zero]
          have h2 := huv P
          rw [hNP, zsmul_zero, add_zero] at h2
          exact h2.symm
        have hmem : u • ((ℓ : ℤ) • (P + Q)) ∈ AddSubgroup.zmultiples (P + Q) :=
          AddSubgroup.zsmul_mem _ (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _) _
        rwa [h1] at hmem
      · rw [AddSubgroup.zmultiples_le]
        have h1 : v • ((N : ℤ) • (P + Q)) = Q := by
          rw [zsmul_add, hNP, zero_add]
          have h2 := huv Q
          rw [hℓQ, zsmul_zero, zero_add] at h2
          exact h2.symm
        have hmem : v • ((N : ℤ) • (P + Q)) ∈ AddSubgroup.zmultiples (P + Q) :=
          AddSubgroup.zsmul_mem _ (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _) _
        rwa [h1] at hmem
    · rw [AddSubgroup.zmultiples_le]
      exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples P))
        (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples Q))
  rw [heq]
  exact ⟨inferInstance, by rw [Nat.card_zmultiples, hord]⟩

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

section MoreSubgroups

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem inf_eq_bot_of_coprime_card {m n : ℕ} (A B : AddSubgroup G) [Finite A] [Finite B]
    (hA : Nat.card A = m) (hB : Nat.card B = n) (h : m.Coprime n) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [AddSubgroup.mem_bot]
  have h1 : addOrderOf (⟨T, hT.1⟩ : A) ∣ m := hA ▸ addOrderOf_dvd_natCard _
  have h2 : addOrderOf (⟨T, hT.2⟩ : B) ∣ n := hB ▸ addOrderOf_dvd_natCard _
  rw [← AddSubgroup.addOrderOf_coe] at h1 h2
  have h3 : addOrderOf T = 1 := Nat.eq_one_of_dvd_coprimes h h1 h2
  exact AddMonoid.addOrderOf_eq_one_iff.mp h3

theorem cyclic_map_of_injOn (f : G →+ H) (A : AddSubgroup G) (n : ℕ)
    (hA : IsAddCyclic A ∧ Nat.card A = n) (hinj : Set.InjOn f A) :
    IsAddCyclic (A.map f) ∧ Nat.card (A.map f) = n := by
  obtain ⟨P, hPA, hP⟩ := exists_zmultiples_eq A hA.1 _ hA.2
  refine ⟨?_, ?_⟩
  · rw [← hPA, AddMonoidHom.map_zmultiples]; infer_instance
  · have hset : ((A.map f : AddSubgroup H) : Set H) = f '' (A : Set G) := AddSubgroup.coe_map f A
    have h1 : Nat.card (A.map f) = Nat.card (f '' (A : Set G)) := by
      rw [← hset]; rfl
    rw [h1, Nat.card_image_of_injOn hinj]
    exact hA.2

end MoreSubgroups

section Count

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
  (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
  (E_x : WeierstrassCurve κ) [E_x.IsElliptic]
  (C_x : AddSubgroup E_x.toAffine.Point) (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N)
  (x : Place κ (modularFunctionFieldC κ N)) (hgx : gPl hNℓ E_x C_x = x)

theorem coprime_of (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : N.Coprime ℓ :=
  (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))

def ellPart (C : CycSub E_x (N * ℓ)) : CycSub E_x N :=
  ⟨C.1.map (ℓ • AddMonoidHom.id _), cyclic_map_nsmul_ell (NeZero.ne ℓ) C.1 C.2⟩

theorem ellPart_val (C : CycSub E_x (N * ℓ)) : (ellPart E_x C).1 = C.1.map (ℓ • AddMonoidHom.id _) := rfl

def mx : ℕ := Nat.card {C' : CycSub E_x N // gPl hNℓ E_x C'.1 = gPl hNℓ E_x C_x}

include hCx in
theorem ord_x_eq : (gPl hNℓ E_x C_x).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E_x.j) =
    (mx hNℓ E_x C_x : ℤ) :=
  g4 hNℓ E_x ⟨C_x, hCx⟩

include hCx in
theorem mx_pos : 0 < mx hNℓ E_x C_x := by
  have h := g1 hNℓ E_x ⟨C_x, hCx⟩
  have h' := ord_x_eq hNℓ E_x C_x hCx
  simp only at h
  omega

include hCx in
theorem finite_fibre_x : Finite {C' : CycSub E_x N // gPl hNℓ E_x C'.1 = gPl hNℓ E_x C_x} :=
  Nat.finite_of_card_ne_zero (mx_pos hNℓ E_x C_x hCx).ne'

theorem restrictAlong_alpha (C : CycSub E_x (N * ℓ)) :
    (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = gPl hNℓ E_x (ellPart E_x C).1 :=
  law_alpha hNℓ hα E_x C (ellPart E_x C) (fun T hT => ⟨T, hT, rfl⟩)

theorem ord_alpha_sub (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    W.ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E_x.j) =
      W.ramificationIndexAlong (heckeAlphaC κ N ℓ) *
        (W.restrictAlong (heckeAlphaC κ N ℓ) hα).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E_x.j) := by
  rw [← Place.ord_restrictAlong, map_sub, AlgHom.commutes]

include hCx hgx in

theorem exists_of_restrictAlong_eq (W : Place κ (charLDegeneracyRoof κ N ℓ))
    (hW : W.restrictAlong (heckeAlphaC κ N ℓ) hα = x) : ∃ C : CycSub E_x (N * ℓ), fPl hNℓ E_x C.1 = W := by
  apply f2 hNℓ E_x W
  rw [ord_alpha_sub hα E_x W, hW, ← hgx, ord_x_eq hNℓ E_x C_x hCx]
  have h1 := ramificationIndexAlong_pos (heckeAlphaC κ N ℓ) hα W
  have h2 := mx_pos hNℓ E_x C_x hCx
  positivity

include hCx hgx in

theorem natCard_fibre_eq (C : CycSub E_x (N * ℓ)) (hC : (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = x) :
    (Nat.card {C' : CycSub E_x (N * ℓ) // fPl hNℓ E_x C'.1 = fPl hNℓ E_x C.1} : ℤ) =
      (fPl hNℓ E_x C.1).ramificationIndexAlong (heckeAlphaC κ N ℓ) * mx hNℓ E_x C_x := by
  rw [← f4 hNℓ E_x C, ord_alpha_sub hα E_x, hC, ← hgx, ord_x_eq hNℓ E_x C_x hCx]

theorem fPl_map_vcMap {γ : VariableChange κ} (hγ : γ • E_x = E_x) (A : CycSub E_x (N * ℓ)) :
    fPl hNℓ E_x (A.1.map (vcMap hγ).toAddMonoidHom) = fPl hNℓ E_x A.1 := by
  have hA' := cyclic_map_equiv (vcMap hγ) A.1 (N * ℓ) A.2
  symm
  exact (f3 hNℓ E_x A ⟨_, hA'⟩).mpr ⟨γ, hγ, (forall_heq_iff hγ A.1 _).mpr fun T hT => ⟨T, hT, rfl⟩⟩

theorem fPl_map_vcMap_symm {γ : VariableChange κ} (hγ : γ • E_x = E_x) (A : CycSub E_x (N * ℓ)) :
    fPl hNℓ E_x (A.1.map (vcMap hγ).symm.toAddMonoidHom) = fPl hNℓ E_x A.1 := by
  have hA' := cyclic_map_equiv (vcMap hγ).symm A.1 (N * ℓ) A.2
  have h := fPl_map_vcMap hNℓ E_x hγ ⟨_, hA'⟩
  rw [← h]
  simp only [map_map_equiv_symm]

include hℓ hℓN hCx hgx in

theorem natCard_orbit (y : Place κ (modularFunctionFieldC κ N)) :
    Nat.card {C : CycSub E_x (N * ℓ) //
        (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧
          (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} =
      mx hNℓ E_x C_x * Nat.card {C : CycSub E_x (N * ℓ) //
        C.1.map (ℓ • AddMonoidHom.id _) = C_x ∧ (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} := by
  classical

  let Φ := {C' : CycSub E_x N // gPl hNℓ E_x C'.1 = gPl hNℓ E_x C_x}
  let SC : AddSubgroup E_x.toAffine.Point → Type := fun B => {C : CycSub E_x (N * ℓ) //
    C.1.map (ℓ • AddMonoidHom.id _) = B ∧ (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y}

  have e1 : {C : CycSub E_x (N * ℓ) //
        (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧
          (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} ≃ Σ C' : Φ, SC C'.1.1 :=
    { toFun := fun C => ⟨⟨ellPart E_x C.1, by rw [← restrictAlong_alpha hNℓ hα E_x C.1, C.2.1, hgx]⟩, C.1, rfl, C.2.2⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 : (ellPart E_x p.2.1).1 = p.1.1.1 := p.2.2.1
          have h2 : gPl hNℓ E_x (ellPart E_x p.2.1).1 = gPl hNℓ E_x C_x := by rw [h1]; exact p.1.2
          rw [restrictAlong_alpha hNℓ hα E_x, h2, hgx], p.2.2.2⟩
      left_inv := fun C => rfl
      right_inv := fun p => by
        refine Sigma.subtype_ext (Subtype.ext (Subtype.ext p.2.2.1)) rfl }

  have e2 : ∀ C' : Φ, Nonempty (SC C'.1.1 ≃ SC C_x) := by
    rintro ⟨C', hC'⟩
    obtain ⟨γ, hγ, hmap⟩ := (g3 hNℓ E_x E_x C' ⟨C_x, hCx⟩).mp hC'
    replace hmap := (forall_heq_iff hγ (C'.1 : Set _) (C_x : Set _)).mp hmap

    let θ : E_x.toAffine.Point ≃+ E_x.toAffine.Point := vcMap hγ
    have hθC' : C'.1.map θ.toAddMonoidHom = C_x := by
      haveI : Finite C_x := Nat.finite_of_card_ne_zero (by rw [hCx.2]; exact NeZero.ne N)
      apply AddSubgroup.eq_of_le_of_card_ge
      · rintro T ⟨S, hS, rfl⟩; exact hmap S hS
      · rw [hCx.2, (cyclic_map_equiv θ C'.1 N C'.2).2]
    have hθC'symm : C_x.map θ.symm.toAddMonoidHom = C'.1 := by
      rw [← hθC', map_equiv_symm_map]
    refine ⟨{ toFun := fun C => ⟨⟨C.1.1.map θ.toAddMonoidHom, cyclic_map_equiv θ C.1.1 _ C.1.2⟩, ?_, ?_⟩
              invFun := fun C => ⟨⟨C.1.1.map θ.symm.toAddMonoidHom, cyclic_map_equiv θ.symm C.1.1 _ C.1.2⟩, ?_, ?_⟩
              left_inv := fun C => Subtype.ext (Subtype.ext (map_equiv_symm_map θ C.1.1))
              right_inv := fun C => Subtype.ext (Subtype.ext (map_map_equiv_symm θ C.1.1)) }⟩
    · show (C.1.1.map θ.toAddMonoidHom).map (ℓ • AddMonoidHom.id _) = C_x
      rw [← map_nsmul_map, C.2.1, hθC']
    · show (fPl hNℓ E_x (C.1.1.map (vcMap hγ).toAddMonoidHom)).restrictAlong (heckeBetaC κ N ℓ) hβ = y
      rw [fPl_map_vcMap hNℓ E_x hγ C.1]; exact C.2.2
    · show (C.1.1.map θ.symm.toAddMonoidHom).map (ℓ • AddMonoidHom.id _) = C'.1
      rw [← map_nsmul_map, C.2.1, hθC'symm]
    · show (fPl hNℓ E_x (C.1.1.map (vcMap hγ).symm.toAddMonoidHom)).restrictAlong (heckeBetaC κ N ℓ) hβ = y
      rw [fPl_map_vcMap_symm hNℓ E_x hγ C.1]; exact C.2.2

  have e3 : (Σ C' : Φ, SC C'.1.1) ≃ Φ × SC C_x :=
    (Equiv.sigmaCongrRight fun C' => (e2 C').some).trans (Equiv.sigmaEquivProd Φ (SC C_x))
  rw [Nat.card_congr (e1.trans e3), Nat.card_prod]
  rfl

include hℓ hℓN hCx in

theorem key_iff (hℓq0 : (ℓ : κ) ≠ 0) (E_y : WeierstrassCurve κ) [E_y.IsElliptic]
    (C_y : AddSubgroup E_y.toAffine.Point) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (y : Place κ (modularFunctionFieldC κ N)) (hgy : gPl hNℓ E_y C_y = y)
    (C : CycSub E_x (N * ℓ)) (hC : C.1.map (ℓ • AddMonoidHom.id _) = C_x) :
    (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y ↔
      ∃ ψ ∈ rationalHomSet κ E_x E_y, ∃ ψ' ∈ rationalHomSet κ E_y E_x,
        ψ.ker = C.1.map (N • AddMonoidHom.id _) ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧
          ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C_x, ψ T ∈ C_y := by
  have hcop : N.Coprime ℓ := coprime_of hℓ hℓN

  obtain ⟨hDc, hDcard⟩ := cyclic_map_nsmul_N (NeZero.ne N) C.1 C.2 (ℓ := ℓ)
  obtain ⟨Q, hQD, hQ⟩ := exists_zmultiples_eq _ hDc ℓ hDcard
  have hQC : Q ∈ C.1 := map_nsmul_le N C.1 (hQD ▸ AddSubgroup.mem_zmultiples Q)

  obtain ⟨A, hA, φ, hφ, hker, huniv, hlaw⟩ := exists_veluData hNℓ hβ hℓ hℓq0 E_x Q hQ
  let φ' : E_x.toAffine.Point →+ A.toAffine.Point := φ
  have hφ'ker : φ'.ker = C.1.map (N • AddMonoidHom.id _) := hker.trans hQD

  haveI : Finite C_x := Nat.finite_of_card_ne_zero (by rw [hCx.2]; exact NeZero.ne N)
  haveI : Finite (C.1.map (N • AddMonoidHom.id E_x.toAffine.Point)) :=
    Nat.finite_of_card_ne_zero (by rw [hDcard]; exact NeZero.ne ℓ)
  have hmeet : C.1.map (N • AddMonoidHom.id _) ⊓ C_x = ⊥ :=
    inf_eq_bot_of_coprime_card _ _ hDcard hCx.2 hcop.symm
  have hinj : Set.InjOn φ' C_x := by
    intro T₁ h₁ T₂ h₂ h12
    have hk : T₁ - T₂ ∈ φ'.ker := by rw [AddMonoidHom.mem_ker, map_sub]; exact sub_eq_zero.mpr h12
    rw [hφ'ker] at hk
    have hb : T₁ - T₂ ∈ C.1.map (N • AddMonoidHom.id _) ⊓ C_x := ⟨hk, C_x.sub_mem h₁ h₂⟩
    rw [hmeet, AddSubgroup.mem_bot] at hb
    exact sub_eq_zero.mp hb

  let C'' : CycSub A N := ⟨C_x.map φ', cyclic_map_of_injOn φ' C_x N hCx hinj⟩
  have hCC'' : ∀ T ∈ C.1, φ' T ∈ C''.1 := by
    intro T hT
    obtain ⟨a, ha, d, hd, rfl⟩ := exists_add_of_mem hcop C.1 hT
    rw [hC] at ha
    have hd0 : φ' d = 0 := by rw [← AddMonoidHom.mem_ker, hφ'ker]; exact hd
    refine ⟨a, ha, ?_⟩
    show φ' a = φ' (a + d)
    rw [map_add, hd0, add_zero]

  rw [hlaw C hQC C'' hCC'', ← hgy, g3 hNℓ A E_y C'' ⟨C_y, hCy⟩]

  have hre : ∀ γ : VariableChange κ,
      (∀ T ∈ C''.1, ∃ T' ∈ C_y, HEq (Point.vcInvFun γ A.toAffine T) T') ↔
        ∀ S ∈ (C_x : Set E_x.toAffine.Point), ∃ T' ∈ (C_y : Set E_y.toAffine.Point),
          HEq (Point.vcInvFun γ A.toAffine (φ S)) T' := by
    intro γ
    constructor
    · intro H S hS
      exact H (φ' S) ⟨S, hS, rfl⟩
    · rintro H T ⟨S, hS, rfl⟩
      exact H S hS
  simp only [hre]
  rw [WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair E_x A E_y hℓ hℓq0 Q hQ φ hφ hker huniv (C_x : Set _) (C_y : Set _),
    hQD]
  exact Iff.rfl

include hℓ hℓN hCx in

theorem natCard_levelStructures_eq (hℓq0 : (ℓ : κ) ≠ 0) (E_y : WeierstrassCurve κ) [E_y.IsElliptic]
    (C_y : AddSubgroup E_y.toAffine.Point) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (y : Place κ (modularFunctionFieldC κ N)) (hgy : gPl hNℓ E_y C_y = y) :
    Nat.card {C : CycSub E_x (N * ℓ) //
        C.1.map (ℓ • AddMonoidHom.id _) = C_x ∧ (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} =
      Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ rationalHomSet κ E_x E_y, ∃ ψ' ∈ rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ∀ T ∈ C_x, ψ T ∈ C_y} := by
  have hcop : N.Coprime ℓ := coprime_of hℓ hℓN
  haveI : Finite C_x := Nat.finite_of_card_ne_zero (by rw [hCx.2]; exact NeZero.ne N)
  have key := key_iff hNℓ hℓ hℓN hβ E_x C_x hCx hℓq0 E_y C_y hCy y hgy

  have hsup : ∀ D : AddSubgroup E_x.toAffine.Point, Nat.card D = ℓ →
      (IsAddCyclic ↥(C_x ⊔ D) ∧ Nat.card ↥(C_x ⊔ D) = N * ℓ) ∧
      (C_x ⊔ D).map (ℓ • AddMonoidHom.id _) = C_x ∧ (C_x ⊔ D).map (N • AddMonoidHom.id _) = D := by
    intro D hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; exact hℓ.ne_zero)
    refine ⟨cyclic_sup hℓ hcop C_x D hCx hD, ?_, ?_⟩
    · rw [AddSubgroup.map_sup, map_nsmul_eq_self_of_coprime C_x hCx.2 hcop.symm, map_nsmul_card_eq_bot D hD,
        sup_bot_eq]
    · rw [AddSubgroup.map_sup, map_nsmul_card_eq_bot C_x hCx.2, map_nsmul_eq_self_of_coprime D hD hcop,
        bot_sup_eq]
  refine Nat.card_congr
    { toFun := fun C => ⟨C.1.1.map (N • AddMonoidHom.id _), (cyclic_map_nsmul_N (NeZero.ne N) C.1.1 C.1.2).2,
        (key C.1 C.2.1).mp C.2.2⟩
      invFun := fun D => ⟨⟨C_x ⊔ D.1, (hsup D.1 D.2.1).1⟩, (hsup D.1 D.2.1).2.1,
        (key ⟨C_x ⊔ D.1, (hsup D.1 D.2.1).1⟩ (hsup D.1 D.2.1).2.1).mpr (by
          have h22 : (C_x ⊔ D.1).map (N • AddMonoidHom.id _) = D.1 := (hsup D.1 D.2.1).2.2
          show ∃ ψ ∈ rationalHomSet κ E_x E_y, ∃ ψ' ∈ rationalHomSet κ E_y E_x,
            ψ.ker = (C_x ⊔ D.1).map (N • AddMonoidHom.id _) ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧
              ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C_x, ψ T ∈ C_y
          rw [h22]; exact D.2.2)⟩
      left_inv := fun C => Subtype.ext (Subtype.ext (by
        have h := map_ell_sup_map_N hcop C.1.1
        rw [C.2.1] at h
        exact h))
      right_inv := fun D => Subtype.ext (hsup D.1 D.2.1).2.2 }

set_option maxHeartbeats 6400000 in
include hℓ hℓN hCx hgx in
open Classical in

theorem finsum_eq_natCard [Fact ℓ.Prime] (hℓq0 : (ℓ : κ) ≠ 0) (E_y : WeierstrassCurve κ) [E_y.IsElliptic]
    (C_y : AddSubgroup E_y.toAffine.Point) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (y : Place κ (modularFunctionFieldC κ N)) (hgy : gPl hNℓ E_y C_y = y) :
    (∑ᶠ W : Place κ (charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧ W.restrictAlong (heckeBetaC κ N ℓ) hβ = y then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      (Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ rationalHomSet κ E_x E_y, ∃ ψ' ∈ rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ∀ T ∈ C_x, ψ T ∈ C_y} : ℤ) := by
  classical
  haveI : HasPrincipalDivisors κ (charLDegeneracyRoof κ N ℓ) :=
    hasPrincipalDivisors_charLDegeneracyRoof κ N ℓ (hN_of hNℓ) hℓq0

  set T : Finset (Place κ (charLDegeneracyRoof κ N ℓ)) := Place.fiberAlong (heckeAlphaC κ N ℓ) hα x with hT
  have hmemT : ∀ W, W ∈ T ↔ W.restrictAlong (heckeAlphaC κ N ℓ) hα = x := fun W => Place.mem_fiberAlong
  have hfibfin : ∀ W : Place κ (charLDegeneracyRoof κ N ℓ), W.restrictAlong (heckeAlphaC κ N ℓ) hα = x →
      Finite {C' : CycSub E_x (N * ℓ) // fPl hNℓ E_x C'.1 = W} := by
    intro W hW
    obtain ⟨C, rfl⟩ := exists_of_restrictAlong_eq hNℓ hα E_x C_x hCx x hgx W hW
    apply Nat.finite_of_card_ne_zero
    have h1 := natCard_fibre_eq hNℓ hα E_x C_x hCx x hgx C hW
    have h2 := ramificationIndexAlong_pos (heckeAlphaC κ N ℓ) hα (fPl hNℓ E_x C.1)
    have h3 := mx_pos hNℓ E_x C_x hCx
    intro h0
    rw [h0, Nat.cast_zero] at h1
    have : (0 : ℤ) < (fPl hNℓ E_x C.1).ramificationIndexAlong (heckeAlphaC κ N ℓ) * mx hNℓ E_x C_x := by positivity
    omega

  rw [finsum_eq_sum_of_support_subset _ (s := T) (by
    intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, hmemT]
    by_contra hx'
    exact hW (if_neg fun h => hx' h.1))]
  set T' := T.filter (fun W => W.restrictAlong (heckeBetaC κ N ℓ) hβ = y) with hT'
  have hLHS : (∑ W ∈ T, if W.restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧ W.restrictAlong (heckeBetaC κ N ℓ) hβ = y then
        (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0) =
      ∑ W ∈ T', (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hWx := (hmemT W).mp hW
    by_cases hWy : W.restrictAlong (heckeBetaC κ N ℓ) hβ = y
    · rw [if_pos ⟨hWx, hWy⟩, if_pos hWy]
    · rw [if_neg fun h => hWy h.2, if_neg hWy]
  rw [hLHS]

  have hmemT' : ∀ W, W ∈ T' → W.restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧ W.restrictAlong (heckeBetaC κ N ℓ) hβ = y :=
    fun W hW => ⟨(hmemT W).mp (Finset.mem_filter.mp hW).1, (Finset.mem_filter.mp hW).2⟩
  haveI : ∀ W : T', Finite {C' : CycSub E_x (N * ℓ) // fPl hNℓ E_x C'.1 = W.1} :=
    fun W => hfibfin W.1 (hmemT' W.1 W.2).1
  have hS : (mx hNℓ E_x C_x : ℤ) * ∑ W ∈ T', (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) =
      Nat.card {C : CycSub E_x (N * ℓ) //
        (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧
          (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} := by
    have hsigma : Nat.card {C : CycSub E_x (N * ℓ) //
        (fPl hNℓ E_x C.1).restrictAlong (heckeAlphaC κ N ℓ) hα = x ∧
          (fPl hNℓ E_x C.1).restrictAlong (heckeBetaC κ N ℓ) hβ = y} =
        Nat.card (Σ W : T', {C' : CycSub E_x (N * ℓ) // fPl hNℓ E_x C'.1 = W.1}) := by
      refine Nat.card_congr
        { toFun := fun C => ⟨⟨fPl hNℓ E_x C.1.1, Finset.mem_filter.mpr ⟨(hmemT _).mpr C.2.1, C.2.2⟩⟩, C.1, rfl⟩
          invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact hmemT' p.1.1 p.1.2⟩
          left_inv := fun C => rfl
          right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2) rfl }
    rw [hsigma, Nat.card_sigma, Finset.sum_coe_sort T' (fun W => Nat.card {C' : CycSub E_x (N * ℓ) // fPl hNℓ E_x C'.1 = W}),
      Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨C, rfl⟩ := exists_of_restrictAlong_eq hNℓ hα E_x C_x hCx x hgx W (hmemT' W hW).1
    rw [natCard_fibre_eq hNℓ hα E_x C_x hCx x hgx C (hmemT' _ hW).1, mul_comm]

  have horbit := natCard_orbit hNℓ hℓ hℓN hα hβ E_x C_x hCx x hgx y
  have hlevel := natCard_levelStructures_eq hNℓ hℓ hℓN hβ E_x C_x hCx hℓq0 E_y C_y hCy y hgy
  rw [horbit, hlevel, Nat.cast_mul] at hS
  have hmx : (mx hNℓ E_x C_x : ℤ) ≠ 0 := by exact_mod_cast (mx_pos hNℓ E_x C_x hCx).ne'
  exact mul_left_cancel₀ hmx hS

end Count

end ModularCurve.RoofCountLevelN
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve.RoofCountLevelN"
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve"

open ModularCurve.RoofCountLevelN in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' N κ))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (C_x : AddSubgroup E_x.toAffine.Point) (C_y : AddSubgroup E_y.toAffine.Point)
    (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (hx : (x.1).toValuationSubring = (moduliPlace κ N E_x C_x).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom)
    (hy : (y.1).toValuationSubring = (moduliPlace κ N E_y C_y).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      (Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          ∀ T ∈ C_x, ψ T ∈ C_y} : ℤ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hq'ℓ : ¬ q' ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hℓ0 : (ℓ : κ) ≠ 0 := fun h => hq'ℓ ((CharP.cast_eq_zero_iff κ q' ℓ).mp h)
  have hN0 : (N : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)
  have hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hN0 hℓ0
  have hgx : gPl hNℓ E_x C_x = x.1 := ((transport_eC_eq_iff hNℓ (moduliPlace κ N E_x C_x) x.1).mpr hx).symm
  have hgy : gPl hNℓ E_y C_y = y.1 := ((transport_eC_eq_iff hNℓ (moduliPlace κ N E_y C_y) y.1).mpr hy).symm
  rw [entry_eq_finsum q' N ℓ hℓ hℓN hNℓ hα hβ x y]
  exact finsum_eq_natCard hNℓ hℓ hℓN hα hβ E_x C_x hCx x.1 hgx hℓ0 E_y C_y hCy y.1 hgy

end
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace.ModularCurve.RoofCountLevelN"

end S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace
end P2MW
export P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_moduliPlace (solution)
