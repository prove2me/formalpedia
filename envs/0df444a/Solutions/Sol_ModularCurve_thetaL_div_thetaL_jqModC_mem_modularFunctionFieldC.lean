-- Prove2me | solution 1 for ModularCurve.thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3608ebf7-ae9e-5ffd-be17-c02eafe454c9

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC.ModularCurve"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC modularFunctionFieldC thetaL thetaL_apply theta_mul isSeparable_jqNModC_of_good coeff_jqModC_neg_one"
namespace M2
p2m_open "ModularCurve"

variable (K : Type*) [Field K]

theorem coeff_thetaL (f : LaurentSeries K) (n : ℤ) : (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_mul' (f g : LaurentSeries K) : thetaL K (f * g) = f * thetaL K g + g * thetaL K f := by
  simp only [thetaL_apply]
  exact theta_mul f g

theorem thetaL_C (c : K) : thetaL K (HahnSeries.C c) = 0 := by
  ext n
  rw [coeff_thetaL, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; simp
  · simp

theorem thetaL_one : thetaL K (1 : LaurentSeries K) = 0 := by
  rw [← map_one HahnSeries.C]; exact thetaL_C K 1

theorem thetaL_inv (x : LaurentSeries K) (hx : x ≠ 0) : thetaL K x⁻¹ = -(x⁻¹ ^ 2) * thetaL K x := by
  have h := thetaL_mul' K x x⁻¹
  rw [mul_inv_cancel₀ hx, thetaL_one] at h
  have h' : x * thetaL K x⁻¹ = -(x⁻¹ * thetaL K x) := eq_neg_of_add_eq_zero_left h.symm
  calc thetaL K x⁻¹ = x⁻¹ * (x * thetaL K x⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    _ = x⁻¹ * -(x⁻¹ * thetaL K x) := by rw [h']
    _ = -(x⁻¹ ^ 2) * thetaL K x := by ring

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp only [coeff_thetaL, coeff_jqModC_neg_one] at h1
  simp at h1

noncomputable def Dj (y : LaurentSeries K) : LaurentSeries K := thetaL K y / thetaL K (jqModC K)

theorem Dj_add (a b : LaurentSeries K) : Dj K (a + b) = Dj K a + Dj K b := by
  simp only [Dj, map_add, add_div]

theorem Dj_mul (a b : LaurentSeries K) : Dj K (a * b) = a * Dj K b + b * Dj K a := by
  simp only [Dj, thetaL_mul']
  ring

theorem main (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldC K N) :
    thetaL K x / thetaL K (jqModC K) ∈ modularFunctionFieldC K N := by
  set F : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))
    with hFdef
  have hT0 := thetaL_jqModC_ne_zero K

  have hF : ∀ y : LaurentSeries K, y ∈ F → Dj K y ∈ F := by
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [Dj, div_self hT0]
      exact one_mem F
    | algebraMap c =>
      have hc : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
        have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
        rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
      rw [Dj, hc, thetaL_C, zero_div]
      exact zero_mem F
    | add y z hy hz ihy ihz =>
      rw [Dj_add]; exact add_mem ihy ihz
    | inv y hy ihy =>
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [inv_zero, Dj, map_zero, zero_div]; exact zero_mem F
      · have : Dj K y⁻¹ = -(y⁻¹ ^ 2) * Dj K y := by
          simp only [Dj, thetaL_inv K y hy0]; ring
        rw [this]
        exact mul_mem (neg_mem (pow_mem (inv_mem hy) 2)) ihy
    | mul y z hy hz ihy ihz =>
      rw [Dj_mul]
      exact add_mem (mul_mem hy ihz) (mul_mem hz ihy)
  have hsep := isSeparable_jqNModC_of_good K N p hpN
  have hx' : x ∈ IntermediateField.adjoin F ({jqNModC K N} : Set (LaurentSeries K)) := by
    change x ∈ IntermediateField.adjoin K {jqModC K, jqNModC K N} at hx
    rw [← IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.mem_restrictScalars] at hx
    exact hx
  have hD := IntermediateField.apply_mem_adjoin_simple_of_leibniz_of_isSeparable (Dj K) (Dj_add K) (Dj_mul K)
    F hF (jqNModC K N) hsep x hx'
  change thetaL K x / thetaL K (jqModC K) ∈ IntermediateField.adjoin K {jqModC K, jqNModC K N}
  rw [← IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.mem_restrictScalars]
  exact hD

end ModularCurve.M2

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC.ModularCurve in
theorem solution (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldC K N) :
    thetaL K x / thetaL K (jqModC K) ∈ modularFunctionFieldC K N :=
  ModularCurve.M2.main K p N hpN x hx

end S_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC (solution)
