-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.norm_factorial_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:03.373596+00:00
-- url     : https://prove2.me/submissions/d6662922-cdd3-4824-9ce9-bdb6a6aa4418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
import Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_natCast_eq_one_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    ‖((n.factorial : C))⁻¹‖ ≤ ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ n := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt : ‖(p : C)‖ < 1 := by rw [h]; exact inv_lt_one_of_one_lt₀ hp1
  obtain ⟨v, m, hm, hv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p
    hp.out.ne_one
  have hval : padicValNat p n.factorial = v := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    rw [hv, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hle : (p - 1) * v ≤ n := by
    rw [← hval, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hle' : ((p : ℝ) - 1) * v ≤ n := by
    have : (((p - 1) * v : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    rwa [Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one] at this
  have hm1 : ‖(m : C)‖ = 1 :=
    norm_natCast_eq_one_of_coprime hlt ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  rw [norm_inv, hv, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hm1, h, mul_one, inv_pow,
    inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith
end GlobalTheory.NearlyPrimitive
