-- Prove2me | solution 1 for ModularCurve.coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9f1dd658-a3f7-5097-9acc-ee89c1e7bca6

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_theta_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order.ModularCurve HahnSeries"

namespace ModularCurve
p2m_export "ModularCurve" "thetaL thetaL_apply theta_coeff theta_mul"
p2m_open "ModularCurve"

namespace DlogSeries

variable {k : Type*} [Field k]

theorem thetaL_single (m : ℤ) (c : k) : thetaL k (single m c) = (m : k) • single m c := by
  ext j
  rw [thetaL_apply, theta_coeff, HahnSeries.coeff_smul, coeff_single]
  split_ifs with h
  · subst h; rw [zsmul_eq_mul, smul_eq_mul]
  · rw [smul_zero, smul_zero]

theorem thetaL_coe (u : PowerSeries k) :
    thetaL k (u : LaurentSeries k) =
      ((PowerSeries.mk fun n => (n : k) * PowerSeries.coeff n u : PowerSeries k) : LaurentSeries k) := by
  ext j
  rw [thetaL_apply, theta_coeff]
  change j • ((u : LaurentSeries k)).coeff j = ((PowerSeries.mk fun n => (n : k) * PowerSeries.coeff n u : PowerSeries k) : LaurentSeries k).coeff j
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [smul_zero]
  · rw [PowerSeries.coeff_mk, zsmul_eq_mul]
    congr 1
    have : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg (not_lt.mp h)
    rw [← this, Int.cast_natCast, Int.natAbs_natCast]

theorem coe_inv (u : PowerSeries k) (hu : PowerSeries.constantCoeff u ≠ 0) :
    ((u : LaurentSeries k))⁻¹ = ((u⁻¹ : PowerSeries k) : LaurentSeries k) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel u hu]
  exact (HahnSeries.ofPowerSeries ℤ k).map_one

theorem inv_mul_thetaL_eq (f : LaurentSeries k) (hf : f ≠ 0) :
    ∃ G : PowerSeries k, PowerSeries.constantCoeff G = 0 ∧
      f⁻¹ * thetaL k f = single 0 ((f.order : ℤ) : k) + (G : LaurentSeries k) := by
  set m : ℤ := f.order with hm
  set u : PowerSeries k := f.powerSeriesPart with hu
  have hu0 : PowerSeries.constantCoeff u ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, LaurentSeries.powerSeriesPart_coeff,
      Nat.cast_zero, add_zero]
    exact fun h => hf (coeff_order_eq_zero.mp h)
  have hf' : f = single m 1 * (u : LaurentSeries k) := (LaurentSeries.single_order_mul_powerSeriesPart f).symm
  have hU : (u : LaurentSeries k) ≠ 0 := by
    intro h
    apply hf
    rw [hf', h, mul_zero]
  have hS : (single m (1 : k) : LaurentSeries k) ≠ 0 := by
    rw [Ne, single_eq_zero_iff]; exact one_ne_zero

  set w : PowerSeries k := PowerSeries.mk fun n => (n : k) * PowerSeries.coeff n u with hw
  refine ⟨u⁻¹ * w, ?_, ?_⟩
  · rw [map_mul, hw, ← PowerSeries.coeff_zero_eq_constantCoeff_apply (φ := PowerSeries.mk _),
      PowerSeries.coeff_mk, Nat.cast_zero, zero_mul, mul_zero]

  have hsm : ((m : k) • single m (1 : k) : LaurentSeries k) = single 0 (m : k) * single m 1 := by
    rw [← C_apply, C_mul_eq_smul]
  have hθ : thetaL k f = single m 1 * thetaL k (u : LaurentSeries k) +
      (u : LaurentSeries k) * (single 0 (m : k) * single m 1) := by
    conv_lhs => rw [hf']
    rw [thetaL_apply, theta_mul, ← thetaL_apply, ← thetaL_apply, thetaL_single, hsm]
  rw [hθ, mul_add, hf', mul_inv, thetaL_coe, ← hw, PowerSeries.coe_mul, ← coe_inv u hu0]
  have h1 : ((single m (1 : k))⁻¹ * ((u : LaurentSeries k))⁻¹) * (single m 1 * (w : LaurentSeries k)) =
      ((u : LaurentSeries k))⁻¹ * (w : LaurentSeries k) := by
    field_simp
  have h2 : ((single m (1 : k))⁻¹ * ((u : LaurentSeries k))⁻¹) *
      ((u : LaurentSeries k) * (single 0 (m : k) * single m 1)) = single 0 ((m : ℤ) : k) := by
    field_simp
  rw [h1, h2, add_comm]

theorem main (f : LaurentSeries k) (hf : f ≠ 0) :
    (∀ n : ℤ, n < 0 → (f⁻¹ * thetaL k f).coeff n = 0) ∧
    (f⁻¹ * thetaL k f).coeff 0 = (f.order : k) := by
  obtain ⟨G, hG0, hG⟩ := inv_mul_thetaL_eq f hf
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [hG, coeff_add, coeff_single_of_ne hn.ne, PowerSeries.coeff_coe, if_pos hn, add_zero]
  · rw [hG, coeff_add, coeff_single_same, PowerSeries.coeff_coe, if_neg (lt_irrefl 0)]
    change ((f.order : ℤ) : k) + PowerSeries.coeff (Int.natAbs 0) G = _
    rw [Int.natAbs_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0, add_zero]

end DlogSeries

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order.ModularCurve in
theorem solution
    (k : Type*) [Field k] (f : LaurentSeries k) (hf : f ≠ 0) :
    (∀ n : ℤ, n < 0 → (f⁻¹ * thetaL k f).coeff n = 0) ∧
    (f⁻¹ * thetaL k f).coeff 0 = (f.order : k) :=
  ModularCurve.DlogSeries.main f hf

end S_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
end P2MW
export P2MW.S_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order (solution)
