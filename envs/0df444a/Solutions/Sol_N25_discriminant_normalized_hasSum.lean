-- Prove2me | solution 1 for N25.discriminant_normalized_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:33.818135+00:00
-- url     : https://prove2.me/submissions/af638c25-592c-4417-8dd9-1517e489cf83

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

open scoped MatrixGroups

namespace N25

/-- Removing the initial q factor from the discriminant leaves the integral eta-unit series. -/
theorem _root_.solution (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n)
      (ModularForm.discriminant τ / Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))) := by
  let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  let d := CuspForm.toModularFormₗ CuspForm.discriminant
  have hp : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    rw [MonoidHom.range_eq_map]
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem
      (show ModularGroup.T ∈ (⊤ : Subgroup SL(2, ℤ)) from Subgroup.mem_top _)]
    exact AddSubgroup.mem_zmultiples 1
  have hs := ModularForm.hasSum_qExpansion d zero_lt_one hp τ
  have hd : (d : UpperHalfPlane → ℂ) = ModularForm.discriminant := rfl
  rw [hd, ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at hs
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one] at hs
  change HasSum (fun n : ℕ =>
    PowerSeries.coeff n (PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.X * ModularCurve.dedekindEtaUnit)) * q ^ n)
    (ModularForm.discriminant τ) at hs
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  have hs'' := hs'.div_const q
  simp only [Finset.sum_range_one, PowerSeries.coeff_map,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul,
    map_zero, zero_mul, sub_zero] at hs''
  have hfun :
      (fun n : ℕ => (Int.castRingHom ℂ) (PowerSeries.coeff n ModularCurve.dedekindEtaUnit) *
        q ^ (n + 1) / q) =
      (fun n : ℕ => ((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) * q ^ n) := by
    funext n
    change (((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) * q ^ (n + 1)) / q =
      ((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) * q ^ n
    rw [pow_succ]
    field_simp [hq0]
  rw [hfun] at hs''
  exact hs''

end N25
