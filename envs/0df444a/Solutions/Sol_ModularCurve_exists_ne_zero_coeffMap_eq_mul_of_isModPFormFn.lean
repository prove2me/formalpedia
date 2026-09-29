-- Prove2me | solution 1 for ModularCurve.exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/66d93a11-f19b-561f-8918-2e55edcf128b

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModularCurve_exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isIntegralElem_coeffMap_of_isIntegral_adjoin_jq
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div
import Theorems.Thm_ModularCurve_exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn
set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqModC_rat map_jqModC jNum constantCoeff_jNum jq modularFunctionFieldFull coeffMap coeffMap_coeff IsModPFormFn exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull isIntegralElem_coeffMap_of_isIntegral_adjoin_jq exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat"
p2m_open "ModularCurve"

open HahnSeries

theorem coeffMap_intCastRingHom_rat_injective :
    Function.Injective (coeffMap (Int.castRingHom ℚ)) := by
  intro x y h
  ext k
  have hk := congrArg (fun z : LaurentSeries ℚ => z.coeff k) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at hk
  exact hk

theorem coeffMap_intCastRingHom_jqModC_int : coeffMap (Int.castRingHom ℚ) (jqModC ℤ) = jq :=
  map_jqModC (Int.castRingHom ℚ)

theorem isUnit_single_neg_one_one : IsUnit (HahnSeries.single (-1 : ℤ) (1 : ℤ) : LaurentSeries ℤ) :=
  isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (1 : ℤ) (1 : ℤ), by
    rw [HahnSeries.single_mul_single]; simp⟩

theorem single_neg_one_mul_C_mul_single_one :
    HahnSeries.single (-1 : ℤ) (1 : ℤ) * (HahnSeries.C (1728 : ℤ) * HahnSeries.single (1 : ℤ) (1 : ℤ)) =
      (1728 : LaurentSeries ℤ) := by
  rw [mul_left_comm, HahnSeries.single_mul_single, HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp only [Int.reduceNeg, neg_add_cancel, add_zero, mul_one]
  exact (HahnSeries.C_apply (1728 : ℤ)).symm.trans (map_ofNat HahnSeries.C 1728)

theorem isUnit_jqModC_int : IsUnit (jqModC ℤ) := by
  refine isUnit_single_neg_one_one.mul (IsUnit.map _ (PowerSeries.isUnit_iff_constantCoeff.mpr ?_))
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
  exact isUnit_one

theorem isUnit_jqModC_int_sub : IsUnit (jqModC ℤ - 1728) := by
  have h : jqModC ℤ - 1728 = HahnSeries.single (-1 : ℤ) (1 : ℤ) *
      HahnSeries.ofPowerSeries ℤ ℤ (jNum.map (Int.castRingHom ℤ) - PowerSeries.C (1728 : ℤ) * PowerSeries.X) := by
    rw [map_sub, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, mul_sub,
      single_neg_one_mul_C_mul_single_one]
    rfl
  rw [h]
  refine isUnit_single_neg_one_one.mul (IsUnit.map _ (PowerSeries.isUnit_iff_constantCoeff.mpr ?_))
  rw [map_sub, map_mul, PowerSeries.constantCoeff_X, mul_zero, sub_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
  exact isUnit_one

end ModularCurve

theorem solution
    (N : ℕ) [NeZero N] (m : ℕ) (X : LaurentSeries ℚ)
    (hXF : X ∈ ModularCurve.modularFunctionFieldFull N)
    (hX : ModularCurve.IsModPFormFn ℚ m X) :
    ∃ (c : ℤ) (Y : LaurentSeries ℤ), c ≠ 0 ∧
      ModularCurve.coeffMap (Int.castRingHom ℚ) Y = algebraMap ℚ (LaurentSeries ℚ) (c : ℚ) * X := by
  classical
  have hinj := ModularCurve.coeffMap_intCastRingHom_rat_injective
  have hφj := ModularCurve.coeffMap_intCastRingHom_jqModC_int
  have hdcast : ∀ z : ℤ, algebraMap ℚ (LaurentSeries ℚ) (z : ℚ) = (z : LaurentSeries ℚ) := fun z => map_intCast _ z
  have h1728 : algebraMap ℚ (LaurentSeries ℚ) 1728 = 1728 := map_ofNat _ 1728

  have hint := hX.1
  rw [ModularCurve.jqModC_rat, h1728] at hint
  obtain ⟨d, hd, hdint⟩ :=
    ModularCurve.exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat ModularCurve.jq _ hint
  rw [hdcast] at hdint

  have hI := ModularCurve.isIntegralElem_coeffMap_of_isIntegral_adjoin_jq _ hdint
  obtain ⟨a, b, hb, hXab⟩ :=
    ModularCurve.exists_eq_coeffMap_div_coeffMap_of_mem_modularFunctionFieldFull N X hXF
  have hφb : ModularCurve.coeffMap (Int.castRingHom ℚ) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  have hXb : X * ModularCurve.coeffMap (Int.castRingHom ℚ) b = ModularCurve.coeffMap (Int.castRingHom ℚ) a := by
    rw [hXab, div_mul_cancel₀ _ hφb]
  have hratio : ∃ a' b' : LaurentSeries ℤ, b' ≠ 0 ∧
      (d : LaurentSeries ℚ) * (X ^ 6 * ModularCurve.jq ^ (4 * m) * (ModularCurve.jq - 1728) ^ (3 * m)) =
        ModularCurve.coeffMap (Int.castRingHom ℚ) a' / ModularCurve.coeffMap (Int.castRingHom ℚ) b' := by
    refine ⟨d * a ^ 6 * ModularCurve.jqModC ℤ ^ (4 * m) * (ModularCurve.jqModC ℤ - 1728) ^ (3 * m), b ^ 6,
      pow_ne_zero _ hb, ?_⟩
    apply eq_div_of_mul_eq ((map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ hb))
    calc (d : LaurentSeries ℚ) * (X ^ 6 * ModularCurve.jq ^ (4 * m) * (ModularCurve.jq - 1728) ^ (3 * m)) *
          ModularCurve.coeffMap (Int.castRingHom ℚ) (b ^ 6)
        = (d : LaurentSeries ℚ) * (X * ModularCurve.coeffMap (Int.castRingHom ℚ) b) ^ 6 *
            ModularCurve.jq ^ (4 * m) * (ModularCurve.jq - 1728) ^ (3 * m) := by
          rw [map_pow]; ring
      _ = _ := by
          rw [hXb]
          simp only [map_mul, map_pow, map_sub, hφj, map_intCast, map_ofNat]
  obtain ⟨Z, hZ⟩ := ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div _ hratio hI

  obtain ⟨u, hu⟩ := ModularCurve.isUnit_jqModC_int
  obtain ⟨v, hv⟩ := ModularCurve.isUnit_jqModC_int_sub
  have hinvj : ModularCurve.coeffMap (Int.castRingHom ℚ) ↑u⁻¹ * ModularCurve.jq = 1 := by
    rw [← hφj, ← hu, ← map_mul, Units.inv_mul, map_one]
  have hφv : ModularCurve.coeffMap (Int.castRingHom ℚ) ↑v = ModularCurve.jq - 1728 := by
    rw [hv, map_sub, hφj, map_ofNat]
  have hinvj' : ModularCurve.coeffMap (Int.castRingHom ℚ) ↑v⁻¹ * (ModularCurve.jq - 1728) = 1 := by
    rw [← hφv, ← map_mul, Units.inv_mul, map_one]

  have h6 : ((d : LaurentSeries ℚ) * X) ^ 6 =
      ModularCurve.coeffMap (Int.castRingHom ℚ) ((d : LaurentSeries ℤ) ^ 5 * Z * ↑u⁻¹ ^ (4 * m) * ↑v⁻¹ ^ (3 * m)) := by
    have hre : ModularCurve.coeffMap (Int.castRingHom ℚ) ((d : LaurentSeries ℤ) ^ 5 * Z * ↑u⁻¹ ^ (4 * m) * ↑v⁻¹ ^ (3 * m)) =
        (d : LaurentSeries ℚ) ^ 6 * X ^ 6 *
          (ModularCurve.coeffMap (Int.castRingHom ℚ) ↑u⁻¹ ^ (4 * m) * ModularCurve.jq ^ (4 * m)) *
          (ModularCurve.coeffMap (Int.castRingHom ℚ) ↑v⁻¹ ^ (3 * m) * (ModularCurve.jq - 1728) ^ (3 * m)) := by
      simp only [map_mul, map_pow, hZ, map_intCast]
      ring
    rw [hre, ← mul_pow (ModularCurve.coeffMap (Int.castRingHom ℚ) ↑u⁻¹) ModularCurve.jq (4 * m),
      ← mul_pow (ModularCurve.coeffMap (Int.castRingHom ℚ) ↑v⁻¹) (ModularCurve.jq - 1728) (3 * m),
      hinvj, hinvj', one_pow, one_pow, mul_one, mul_one, mul_pow]
  have hI2 : (ModularCurve.coeffMap (Int.castRingHom ℚ)).IsIntegralElem ((d : LaurentSeries ℚ) * X) := by
    refine ⟨Polynomial.X ^ 6 - Polynomial.C ((d : LaurentSeries ℤ) ^ 5 * Z * ↑u⁻¹ ^ (4 * m) * ↑v⁻¹ ^ (3 * m)),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h6, sub_self]
  have hratio2 : ∃ a' b' : LaurentSeries ℤ, b' ≠ 0 ∧ (d : LaurentSeries ℚ) * X =
      ModularCurve.coeffMap (Int.castRingHom ℚ) a' / ModularCurve.coeffMap (Int.castRingHom ℚ) b' :=
    ⟨d * a, b, hb, by rw [hXab, map_mul, map_intCast, mul_div_assoc]⟩
  obtain ⟨Y, hY⟩ := ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div _ hratio2 hI2
  exact ⟨d, Y, hd, by rw [hY, hdcast]⟩

end S_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn
end P2MW
export P2MW.S_ModularCurve_exists_ne_zero_coeffMap_eq_mul_of_isModPFormFn (solution)
