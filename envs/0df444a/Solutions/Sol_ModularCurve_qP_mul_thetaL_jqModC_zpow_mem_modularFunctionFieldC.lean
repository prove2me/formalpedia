-- Prove2me | solution 1 for ModularCurve.qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/370c3e45-a658-51ca-9596-9df92c589595

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_SwdAlgebra
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModularCurve_qP_mul_thetaL_jqModC_zpow_mul_eq
import Theorems.Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem thetaL thetaL_apply jqModC_ne_zero_def coeff_jqModC_neg_one qP_mul_thetaL_jqModC_zpow_mul_eq thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq"
namespace RBMem
p2m_open "ModularCurve"

theorem coeff_thetaL (K : Type*) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp only [coeff_thetaL, coeff_jqModC_neg_one] at h1
  simp at h1

theorem jqModC_sub_ne_zero (K : Type*) [Field K] (c : K) : jqModC K - HahnSeries.C c ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp [HahnSeries.C_apply] at h1
  rw [coeff_jqModC_neg_one] at h1
  exact one_ne_zero h1

theorem algebraMap_eq_C (K : Type*) [Field K] (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) ∈
      modularFunctionFieldC K N := by
  set F := modularFunctionFieldC K N with hFdef
  obtain ⟨h, hh, -, -⟩ := exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 N hpN K
  have hF2 := qP_mul_thetaL_jqModC_zpow_mul_eq p hp5 K
  rw [← hh, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    map_ofNat, map_ofNat] at hF2
  set T : LaurentSeries K := thetaL K (jqModC K) with hTdef
  set J : LaurentSeries K := jqModC K with hJdef
  set I : LaurentSeries K := HahnSeries.C ((2 : K)⁻¹) with hIdef
  set b : LaurentSeries K := HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * T ^ (-(((p : ℤ) + 1) / 2)) with hbdef
  have hT0 : T ≠ 0 := thetaL_jqModC_ne_zero K
  have hJ0 : J ≠ 0 := jqModC_ne_zero_def K
  have hJ' : J - 1728 ≠ 0 := by
    rw [hJdef, ← map_ofNat HahnSeries.C 1728]
    exact jqModC_sub_ne_zero K 1728
  have hJF : J ∈ F := jqModC_mem K N
  have hhF : (h : LaurentSeries K) ∈ F := h.2
  have hD : thetaL K (h : LaurentSeries K) / T ∈ F :=
    thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC K p N hpN (h : LaurentSeries K) h.2

  have hb : b = (12 * (thetaL K (h : LaurentSeries K) / T) * J * (J - 1728)
      - I * (14 * J - 13824) * (h : LaurentSeries K)) / (J * (J - 1728)) := by
    rw [eq_div_iff (mul_ne_zero hJ0 hJ')]
    field_simp
    linear_combination hF2
  rw [hb]
  have h12 : (12 : LaurentSeries K) ∈ F := by exact_mod_cast natCast_mem F 12
  have h14 : (14 : LaurentSeries K) ∈ F := by exact_mod_cast natCast_mem F 14
  have h1728 : (1728 : LaurentSeries K) ∈ F := by exact_mod_cast natCast_mem F 1728
  have h13824 : (13824 : LaurentSeries K) ∈ F := by exact_mod_cast natCast_mem F 13824
  have hI : I ∈ F := by
    rw [hIdef, ← algebraMap_eq_C]
    exact IntermediateField.algebraMap_mem F _
  refine div_mem (sub_mem ?_ ?_) (mul_mem hJF (sub_mem hJF h1728))
  · exact mul_mem (mul_mem (mul_mem h12 hD) hJF) (sub_mem hJF h1728)
  · exact mul_mem (mul_mem hI (sub_mem (mul_mem h14 hJF) h13824)) hhF

end ModularCurve.RBMem

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC.ModularCurve in
theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] :
    HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) ∈
      modularFunctionFieldC K N :=
  ModularCurve.RBMem.main p hp5 N hpN K

end S_ModularCurve_qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC (solution)
