-- Prove2me | solution 1 for ModularCurve.neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8c0ed515-e281-5228-9b41-1d2c32410ee4

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_SSCarrier
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_ModularCurve_ord_unif
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "placeRamificationJ placeWidth ssPlaces jGeomGen modularFunctionFieldC jWidth charLDegeneracyRoof heckeAlphaC heckeBetaC weightDivisor weightDivisor_apply SSIndex poleOrder lead placeRamificationJ_dvd_jWidth_of_mem_ssPlaces weightFloor_eq_of_isAffineGeomPlace exists_divisor_forall_eq_weightFloor_fieldC"
namespace LiftIndep
p2m_open "ModularCurve"

theorem jWidth_le_three {K : Type*} [Field K] [DecidableEq K] (j : K) : jWidth j ≤ 3 := by
  unfold jWidth; split_ifs <;> omega

theorem one_le_jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : 1 ≤ jWidth j := by
  unfold jWidth; split_ifs <;> omega

theorem evalAt_eq_zero_of_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf0 : f ≠ 0) (hpos : 0 < v.ord f) : v.evalAt f = 0 := by
  have hmem : f ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hf0 hpos.le
  rw [Place.evalAt_congr v hmem (zero_mem _) (Or.inr (by rwa [sub_zero])),
    show (0 : F) = algebraMap K F 0 from (map_zero _).symm, Place.evalAt_algebraMap]

theorem ineq_floor (ux uz ea eb r s m a Dz O : ℤ) (hux : 0 < ux) (huz : 0 < uz) (heb : 0 ≤ eb)
    (hDz1 : uz * Dz ≤ m * (uz * s - 1)) (h2 : ux * a = m * (ux * r - 1)) (h3 : ea * uz = eb * ux) (hO : -Dz ≤ O) :
    -(ea * a) ≤ eb * O + m * (eb * s - ea * r) := by
  have hO' : -(eb * Dz) ≤ eb * O := by nlinarith
  have E : ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * a) = ux * eb * (m * (uz * s - 1) - uz * Dz) := by
    linear_combination (uz * ea) * h2 - m * h3
  have hpos : 0 < ux * uz := mul_pos hux huz
  have hnn : 0 ≤ ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * a) := by
    rw [E]; exact mul_nonneg (mul_nonneg hux.le heb) (by linarith)
  have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  linarith

theorem ineq_index (ux uz ea eb r s m a az O : ℤ) (hux : 0 < ux) (huz : 0 < uz) (heb : 1 ≤ eb)
    (h1 : uz * az = m * (uz * s - 1)) (h2 : ux * a = m * (ux * r - 1)) (h3 : ea * uz = eb * ux)
    (hO : 1 - az ≤ O) :
    -(ea * a) + 1 ≤ eb * O + m * (eb * s - ea * r) := by
  have hO' : eb * (1 - az) ≤ eb * O := mul_le_mul_of_nonneg_left hO (by omega)
  have E : ux * uz * (eb * (1 - az) + m * (eb * s - ea * r) + ea * a - 1) = ux * uz * (eb - 1) := by
    linear_combination (-(ux * eb)) * h1 + (uz * ea) * h2 - m * h3
  have hpos : 0 < ux * uz := mul_pos hux huz
  have hnn : 0 ≤ ux * uz * (eb * (1 - az) + m * (eb * s - ea * r) + ea * a - 1) := by
    rw [E]; exact mul_nonneg hpos.le (by omega)
  have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  linarith

theorem ineq_nonindex (ux uz ea eb r s m a Dz O : ℤ) (hux1 : 1 ≤ ux) (hux3 : ux ≤ 3) (huz1 : 1 ≤ uz) (huz3 : uz ≤ 3)
    (hea : 1 ≤ ea) (heb : 1 ≤ eb)
    (hDz1 : uz * Dz ≤ m * (uz * s - 1)) (hDz2 : m * (uz * s - 1) < uz * (Dz + 1))
    (h2 : ux * a = m * (ux * r - 1)) (h3 : ea * uz = eb * ux)
    (huxm : ux ∣ m) (huzm : ¬ uz ∣ m) (hO : -Dz ≤ O) :
    -(ea * a) + 1 ≤ eb * O + m * (eb * s - ea * r) := by

  set T := m * (uz * s - 1) - uz * Dz with hT
  have hT1 : 0 ≤ T := by omega
  have hT0 : T ≠ 0 := by
    intro h0
    apply huzm
    refine ⟨m * s - Dz, ?_⟩
    have : m * (uz * s - 1) - uz * Dz = 0 := by rw [← hT]; exact h0
    linarith
  have hT1' : 1 ≤ T := by omega
  have hO' : -(eb * Dz) ≤ eb * O := by nlinarith

  have E : ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * a - 1) = ux * (eb * T - uz) := by
    rw [hT]; linear_combination (uz * ea) * h2 - m * h3

  have key : uz ≤ eb * T := by
    interval_cases uz
    · exact absurd (one_dvd m) huzm
    · interval_cases ux
      · have heb2 : 2 ≤ eb := by omega
        nlinarith [heb2, hT1']
      · exact absurd huxm huzm
      · have heb2 : 2 ≤ eb := by omega
        nlinarith [heb2, hT1']
    · interval_cases ux
      · have heb3 : 3 ≤ eb := by omega
        nlinarith [heb3, hT1']
      · have heb3 : 3 ≤ eb := by omega
        nlinarith [heb3, hT1']
      · exact absurd huxm huzm
  have hux : 0 < ux := by omega
  have hpos : 0 < ux * uz := mul_pos hux (by omega)
  have hnn : 0 ≤ ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * a - 1) := by
    rw [E]; exact mul_nonneg hux.le (by linarith)
  have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  linarith

end ModularCurve.LiftIndep

open ModularCurve.LiftIndep in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (m : ℕ) (hm : 1 ≤ m) (h : ↥(charLDegeneracyRoof K N ℓ)) (hh0 : h ≠ 0)
    (d : ↥(modularFunctionFieldC K N)) (hd0 : d ≠ 0)
    (hF : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K →
      -(ModularCurve.weightDivisor K N m z) ≤ z.ord d)
    (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x.1)
    (hH : ∀ y ∈ S,
      y.ord h = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ)
                  * (placeRamificationJ N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
              - (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeRamificationJ N x.1 : ℤ))
    (hW : ∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x.1 : ℤ))
    (hS : ∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K) :
    ∀ y ∈ S, -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ)
        * ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x) ≤ y.ord (heckeBetaC K N ℓ d * h ^ m) := by
  classical
  intro y hy
  set a := ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x with ha_def
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  have hex := ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m

  obtain ⟨hxss, -, -, hxdvd, -⟩ := x.2
  have hux0 : placeWidth N x.1 ≠ 0 := by
    intro h0; rcases hxdvd with ⟨c, hc⟩; rw [h0] at hc; push_cast at hc; omega
  have hWx : placeRamificationJ N x.1 ∣ jWidth (x.1.evalAt (jGeomGen K N)) :=
    ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hxss
  have hux_eq : placeWidth N x.1 * placeRamificationJ N x.1 = jWidth (x.1.evalAt (jGeomGen K N)) :=
    Nat.div_mul_cancel hWx
  have h2 : (placeWidth N x.1 : ℤ) * a = (m : ℤ) * ((placeWidth N x.1 : ℤ) * (placeRamificationJ N x.1 : ℤ) - 1) := by
    rw [ha_def]; unfold ModularCurve.poleOrder
    rw [Int.mul_ediv_cancel' (dvd_mul_of_dvd_left hxdvd _)]
    have : ((jWidth (x.1.evalAt (jGeomGen K N)) : ℤ)) = (placeWidth N x.1 : ℤ) * (placeRamificationJ N x.1 : ℤ) := by
      exact_mod_cast hux_eq.symm
    rw [this]; congr 1; omega
  have huxm : (placeWidth N x.1 : ℤ) ∣ (m : ℤ) := by rcases hxdvd with ⟨c, hc⟩; exact ⟨c, by omega⟩

  set z := y.restrictAlong (heckeBetaC K N ℓ) hβ with hz_def
  have hz : z ∈ ssPlaces p N K := hS y hy
  have hWz : placeRamificationJ N z ∣ jWidth (z.evalAt (jGeomGen K N)) :=
    ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hz
  have huz_eq : placeWidth N z * placeRamificationJ N z = jWidth (z.evalAt (jGeomGen K N)) := Nat.div_mul_cancel hWz
  have huz0 : placeWidth N z ≠ 0 := by
    intro h0; rw [h0, zero_mul] at huz_eq; exact absurd huz_eq.symm (by have := one_le_jWidth (z.evalAt (jGeomGen K N)); omega)

  have hDz : ModularCurve.weightDivisor K N m z = ((m : ℤ) * ((jWidth (z.evalAt (jGeomGen K N)) : ℤ) - 1)) / (placeWidth N z : ℤ) := by
    rw [ModularCurve.weightDivisor_apply K N m hex z, ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K m z hz.2.1]
  have hfloor := hF z hz

  have hβd0 : heckeBetaC K N ℓ d ≠ 0 := (map_ne_zero_iff _ (heckeBetaC K N ℓ).injective).mpr hd0
  have hordg : y.ord (heckeBetaC K N ℓ d * h ^ m) = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * z.ord d + (m : ℤ) * y.ord h := by
    rw [y.ord_mul hβd0 (pow_ne_zero m hh0), ← zpow_natCast, y.ord_zpow, hz_def,
      Place.ord_restrictAlong (heckeBetaC K N ℓ) hβ y d]
  rw [hordg, hH y hy]

  have heb : 1 ≤ (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) := by
    have h0 : 0 < Place.ramificationIndexAlong (heckeBetaC K N ℓ) y := by
      unfold Place.ramificationIndexAlong
      letI := AlgebraicCurve.algebraAlong (heckeBetaC K N ℓ)
      haveI := AlgebraicCurve.isIntegral_along (heckeBetaC K N ℓ) hβ
      exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldC K N)) (w := y)
    exact_mod_cast h0
  have hea : 1 ≤ (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) := by
    have h0 : 0 < Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y := by
      unfold Place.ramificationIndexAlong
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      haveI := AlgebraicCurve.isIntegral_along (heckeAlphaC K N ℓ) hα
      exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldC K N)) (w := y)
    exact_mod_cast h0
  have h3 := hW y hy

  have hux3 : (placeWidth N x.1 : ℤ) ≤ 3 := by
    have := Nat.div_le_self (jWidth (x.1.evalAt (jGeomGen K N))) (placeRamificationJ N x.1)
    have := jWidth_le_three (x.1.evalAt (jGeomGen K N))
    unfold placeWidth; exact_mod_cast (by omega)
  have huz3 : (placeWidth N z : ℤ) ≤ 3 := by
    have := Nat.div_le_self (jWidth (z.evalAt (jGeomGen K N))) (placeRamificationJ N z)
    have := jWidth_le_three (z.evalAt (jGeomGen K N))
    unfold placeWidth; exact_mod_cast (by omega)
  have hWz_int : ((jWidth (z.evalAt (jGeomGen K N)) : ℤ)) = (placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) := by
    exact_mod_cast huz_eq.symm

  have hMz : ModularCurve.weightDivisor K N m z = ((m : ℤ) * ((placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) - 1)) / (placeWidth N z : ℤ) := by
    rw [hDz, hWz_int]
  have huzpos : 0 < (placeWidth N z : ℤ) := by omega
  have hDz1 : (placeWidth N z : ℤ) * ModularCurve.weightDivisor K N m z ≤ (m : ℤ) * ((placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) - 1) := by
    rw [hMz]
    have h' := Int.ediv_mul_le ((m : ℤ) * ((placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) - 1)) huzpos.ne'
    nlinarith [h']
  exact ineq_floor _ _ _ _ _ _ _ _ _ _ (by omega) huzpos (by omega) hDz1 h2 h3 hfloor

end S_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
end P2MW
export P2MW.S_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow (solution)
