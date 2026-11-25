-- Prove2me | solution 1 for GroundTheory.PAdicHodge.log_pow_coeff_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:12.712804+00:00
-- url     : https://prove2.me/submissions/dce88e7e-cb00-45d2-af9c-f69ca21c2cba

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Theorems.Thm_GroundTheory_PAdicHodge_sum_coeff_one_add_X_pow_sub_one_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
namespace GroundTheory.PAdicHodge
theorem _root_.solution (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by
  apply Int.cast_injective (α := ℚ)
  have hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := fun n => by
    rw [← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]
    simp [Polynomial.map_pow]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hcoe]
  have hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n := fun n hn => by
    have h1 := (Finset.mem_Icc.1 hn)
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]
  have hfac : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  calc ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) *
        ((((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m) * (m.factorial / n)
      = m.factorial * ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
        (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = (-1) ^ (m - 1) * q * (m - 1).factorial := by
        rw [sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]
        field_simp
end GroundTheory.PAdicHodge
