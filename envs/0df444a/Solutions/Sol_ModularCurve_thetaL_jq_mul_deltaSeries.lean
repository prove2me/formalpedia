-- Prove2me | solution 1 for ModularCurve.thetaL_jq_mul_deltaSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/203004d2-1ded-585d-8ad5-d584c9ae13c7

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta
import Theorems.Thm_ModularCurve_theta_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_jq_mul_deltaSeries
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_thetaL_jq_mul_deltaSeries.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "eisenstein6 laurentOfInt laurentOfInt_apply eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jNumQ jq dedekindEtaUnitQ deltaSeries deltaSeries_ne_zero thetaL thetaL_apply eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta theta_mul" namespace RC18C3 end ModularCurve.RC18C3
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.RC18C3.jq_mul_deltaSeries :
    jq * deltaSeries = laurentOfInt ℚ (eisenstein4 ^ 3) := by
  have hι : ∀ f : PowerSeries ℤ,
      HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) f) = laurentOfInt ℚ f := fun f => rfl
  rw [jq, deltaSeries, dedekindEtaUnitQ, jNumQ, jNum, hι, hι, mul_mul_mul_comm, HahnSeries.single_mul_single,
    ← map_mul, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_one,
    show (-1 : ℤ) + 1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.RC18C3.deltaSeries_eq_laurentOfInt :
    deltaSeries = laurentOfInt ℚ (PowerSeries.X * dedekindEtaUnit) := by
  rw [deltaSeries, dedekindEtaUnitQ, map_mul, laurentOfInt_apply, laurentOfInt_apply, PowerSeries.map_X,
    HahnSeries.ofPowerSeries_X]

theorem solution :
    thetaL ℚ jq * deltaSeries =
      -(HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (eisenstein4 ^ 2 * eisenstein6))) := by
  have hι : ∀ f : PowerSeries ℤ,
      HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) f) = laurentOfInt ℚ f := fun f => rfl

  have hC2 := ModularCurve.eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta
  rw [hι, hι, hι, ← ModularCurve.RC18C3.deltaSeries_eq_laurentOfInt] at hC2

  have hjΔ := ModularCurve.RC18C3.jq_mul_deltaSeries
  rw [map_pow] at hjΔ
  have hL := ModularCurve.theta_mul jq deltaSeries
  rw [hjΔ, show laurentOfInt ℚ eisenstein4 ^ 3 =
      laurentOfInt ℚ eisenstein4 * laurentOfInt ℚ eisenstein4 * laurentOfInt ℚ eisenstein4 by ring,
    ModularCurve.theta_mul (laurentOfInt ℚ eisenstein4 * laurentOfInt ℚ eisenstein4) (laurentOfInt ℚ eisenstein4),
    ModularCurve.theta_mul (laurentOfInt ℚ eisenstein4) (laurentOfInt ℚ eisenstein4)] at hL
  simp only [thetaL_apply] at hC2 ⊢
  rw [hι, map_mul, map_pow]
  apply mul_right_cancel₀ deltaSeries_ne_zero
  linear_combination (-deltaSeries) * hL + (-(laurentOfInt ℚ eisenstein4) ^ 2) * hC2 +
    (-((HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) * LaurentSeries.derivative ℚ deltaSeries)) * hjΔ

end S_ModularCurve_thetaL_jq_mul_deltaSeries
end P2MW
export P2MW.S_ModularCurve_thetaL_jq_mul_deltaSeries (solution)
