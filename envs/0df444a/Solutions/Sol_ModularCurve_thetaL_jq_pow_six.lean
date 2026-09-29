-- Prove2me | solution 1 for ModularCurve.thetaL_jq_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e38dee5b-584d-5e68-b936-28316792db8a

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
import Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_jq_pow_six
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "HahnSeries ModularCurve P2MW.S_ModularCurve_thetaL_jq_pow_six.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "eisenstein4 constantCoeff_eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jq dedekindEtaUnitQ deltaSeries thetaL eisenstein6 thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6 eisenstein4_cube_sub_mk_sq"
namespace K2c1
p2m_open "ModularCurve"

theorem main : thetaL ℚ jq ^ 6 = jq ^ 4 * (jq - 1728) ^ 3 * deltaSeries := by

  set L : PowerSeries ℤ →+* LaurentSeries ℚ :=
    (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (Int.castRingHom ℚ)) with hL
  have hLapp : ∀ f, L f = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) f) := fun f => rfl
  set e4 := L eisenstein4 with he4
  set e6 := L eisenstein6 with he6
  set T := thetaL ℚ jq with hT

  have hR : T * e4 = -(jq * e6) := by
    rw [hT, he4, he6, hLapp, hLapp]; exact thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6

  have hΔ : deltaSeries = L (PowerSeries.X * dedekindEtaUnit) := by
    rw [deltaSeries, dedekindEtaUnitQ, hLapp, map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]
  have hE : e4 ^ 3 - e6 ^ 2 = 1728 * deltaSeries := by
    have h := congrArg L eisenstein4_cube_sub_mk_sq
    rw [map_sub, map_pow, map_pow, map_mul, map_ofNat] at h
    rw [hΔ, he4, he6]
    exact h

  have hJ : jq * deltaSeries = e4 ^ 3 := by
    have hjq : jq = HahnSeries.single (-1 : ℤ) (1 : ℚ) * L jNum := by
      rw [hLapp]; rfl
    have hinv : L dedekindEtaUnitInv * L dedekindEtaUnit = 1 := by
      rw [← map_mul, mul_comm, dedekindEtaUnit_mul_inv, map_one]
    have hss : HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.single (1 : ℤ) (1 : ℚ) = 1 := by
      rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one]; rfl
    have hXu : L (PowerSeries.X * dedekindEtaUnit) = HahnSeries.single (1 : ℤ) (1 : ℚ) * L dedekindEtaUnit := by
      rw [map_mul, hLapp PowerSeries.X, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
    rw [hjq, hΔ, hXu, jNum, map_mul, map_pow, ← he4]
    calc HahnSeries.single (-1 : ℤ) (1 : ℚ) * (e4 ^ 3 * L dedekindEtaUnitInv) *
          (HahnSeries.single (1 : ℤ) (1 : ℚ) * L dedekindEtaUnit)
        = e4 ^ 3 * (HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.single (1 : ℤ) (1 : ℚ)) *
            (L dedekindEtaUnitInv * L dedekindEtaUnit) := by ring
      _ = e4 ^ 3 := by rw [hss, hinv, mul_one, mul_one]

  have he40 : e4 ≠ 0 := by
    have hc : e4.coeff 0 = 1 := by
      rw [he4, hLapp, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_eisenstein4, map_one]
    intro h0
    rw [h0, HahnSeries.coeff_zero] at hc
    exact zero_ne_one hc

  have h1 : T ^ 6 * e4 ^ 6 = jq ^ 6 * e6 ^ 6 := by
    rw [← mul_pow, hR, neg_pow, mul_pow]; norm_num
  have h2 : (jq - 1728) * deltaSeries = e6 ^ 2 := by
    have : (jq - 1728) * deltaSeries = jq * deltaSeries - 1728 * deltaSeries := by ring
    rw [this, hJ, ← hE]; ring
  have h3 : jq ^ 4 * (jq - 1728) ^ 3 * deltaSeries * e4 ^ 6 = jq ^ 6 * e6 ^ 6 := by
    have e46 : e4 ^ 6 = (jq * deltaSeries) ^ 2 := by rw [hJ]; ring
    rw [e46]
    calc jq ^ 4 * (jq - 1728) ^ 3 * deltaSeries * (jq * deltaSeries) ^ 2
        = jq ^ 6 * ((jq - 1728) * deltaSeries) ^ 3 := by ring
      _ = jq ^ 6 * e6 ^ 6 := by rw [h2]; ring
  exact mul_right_cancel₀ (pow_ne_zero 6 he40) (h1.trans h3.symm)

end ModularCurve.K2c1

theorem solution : ModularCurve.thetaL ℚ ModularCurve.jq ^ 6 = ModularCurve.jq ^ 4 * (ModularCurve.jq - 1728) ^ 3 * ModularCurve.deltaSeries :=
  ModularCurve.K2c1.main

end S_ModularCurve_thetaL_jq_pow_six
end P2MW
export P2MW.S_ModularCurve_thetaL_jq_pow_six (solution)
