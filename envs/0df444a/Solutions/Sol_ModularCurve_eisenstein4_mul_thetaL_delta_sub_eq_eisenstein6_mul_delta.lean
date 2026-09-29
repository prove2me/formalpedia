-- Prove2me | solution 1 for ModularCurve.eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/49f406ed-791b-5230-989a-2bd7c0b49f4a

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularForm_qExpansion_E4_mul_theta_discriminant_sub
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_theta_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "eisenstein6 eisenstein4 dedekindEtaUnit ofPowerSeries_coeff_of_neg thetaL thetaL_apply qExpansion_E4_eq_map_eisenstein4 qExpansion_E6_eq_map_mk qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit theta_coeff"
namespace RC18Transfer
p2m_open "ModularCurve"

noncomputable def thetaPS {R : Type*} [CommSemiring R] (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => (n : R) * f.coeff n

theorem coeff_thetaPS {R : Type*} [CommSemiring R] (f : PowerSeries R) (n : ℕ) :
    (thetaPS f).coeff n = (n : R) * f.coeff n := by
  simp [thetaPS, PowerSeries.coeff_mk]

theorem thetaPS_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (f : PowerSeries R) : PowerSeries.map φ (thetaPS f) = thetaPS (PowerSeries.map φ f) := by
  ext n
  simp [coeff_thetaPS, PowerSeries.coeff_map]

theorem ofPowerSeries_thetaPS (f : PowerSeries ℚ) :
    HahnSeries.ofPowerSeries ℤ ℚ (thetaPS f) = thetaL ℚ (HahnSeries.ofPowerSeries ℤ ℚ f) := by
  ext k
  rw [thetaL_apply, ModularCurve.theta_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, smul_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, coeff_thetaPS,
      zsmul_eq_mul, Int.cast_natCast]

end ModularCurve.RC18Transfer

open ModularCurve.RC18Transfer in
theorem solution :
    HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4) *
        thetaL ℚ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit)))
      - 3 * thetaL ℚ (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein4)) *
        HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit))
      = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) eisenstein6) *
        HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X * dedekindEtaUnit)) := by

  have hE6 : eisenstein6 =
      (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := rfl
  have hZ : eisenstein4 * thetaPS (PowerSeries.X * dedekindEtaUnit)
      - 3 * thetaPS eisenstein4 * (PowerSeries.X * dedekindEtaUnit)
      = eisenstein6 * (PowerSeries.X * dedekindEtaUnit) := by
    apply PowerSeries.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    have hC := ModularForm.qExpansion_E4_mul_theta_discriminant_sub
    rw [ModularCurve.qExpansion_E4_eq_map_eisenstein4, ModularCurve.qExpansion_E6_eq_map_mk,
      ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at hC
    have e1 : (PowerSeries.mk fun n : ℕ =>
        (n : ℂ) * (PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * dedekindEtaUnit)).coeff n) =
        PowerSeries.map (Int.castRingHom ℂ) (thetaPS (PowerSeries.X * dedekindEtaUnit)) := by
      rw [thetaPS_map]; rfl
    have e2 : (PowerSeries.mk fun n : ℕ =>
        (n : ℂ) * (PowerSeries.map (Int.castRingHom ℂ) eisenstein4).coeff n) =
        PowerSeries.map (Int.castRingHom ℂ) (thetaPS eisenstein4) := by
      rw [thetaPS_map]; rfl
    rw [e1, e2] at hC
    simpa [hE6, map_mul, map_sub, map_ofNat] using hC

  let ψ : PowerSeries ℤ →+* LaurentSeries ℚ :=
    (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (Int.castRingHom ℚ))
  have hψ : ∀ f : PowerSeries ℤ, ψ f = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.map (Int.castRingHom ℚ) f) :=
    fun f => rfl
  have hθ : ∀ f : PowerSeries ℤ, ψ (thetaPS f) = thetaL ℚ (ψ f) := by
    intro f
    rw [hψ, hψ, thetaPS_map, ofPowerSeries_thetaPS]
  have key := congrArg ψ hZ
  simp only [map_sub, map_mul, map_ofNat, hθ] at key
  simpa only [hψ, map_mul] using key

end

end S_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta
end P2MW
export P2MW.S_ModularCurve_eisenstein4_mul_thetaL_delta_sub_eq_eisenstein6_mul_delta (solution)
