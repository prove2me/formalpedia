-- Prove2me | solution 1 for ModularCurve.SiegelUnit.siegelFun_add_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7885338a-03c6-5723-bfdc-f159e41bb45b

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_siegelFun_add_level

set_option autoImplicit false

open ModularCurve

noncomputable section

open Complex
open scoped Real

namespace SiegelPerE96

def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

theorem qq_ne_zero (τ : ℂ) : qq τ ≠ 0 := Complex.exp_ne_zero _

theorem qa_ne_zero (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s τ ≠ 0 := Complex.exp_ne_zero _

theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem qa_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N r (s + N) z = qa N r s z := by
  unfold qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [show 2 * (π : ℂ) * I * ((r : ℂ) * z + ((s : ℂ) + (N : ℂ))) / (N : ℂ)
      = 2 * π * I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ) + 2 * π * I by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem pref_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N r (s + N) z = cexp (π * I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * pref N r s z := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u : ℂ, cexp u * (-cexp x * cexp y) = -cexp (u + x) * cexp y from
    fun x y u => by rw [Complex.exp_add]; ring]
  congr 3
  push_cast
  field_simp
  ring

theorem sprod_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    sprod N r (s + N) z = sprod N r s z := by
  unfold sprod
  simp only [qa_add_level N hN]

theorem qa_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N (r + N) s z = qq z * qa N r s z := by
  unfold qa qq
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem pref_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N (r + N) s z = pref N r s z * (qa N r s z * cexp (-(π * I * (s : ℂ) / (N : ℂ)))) := by
  unfold pref qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u v : ℂ, -cexp x * cexp y * (cexp u * cexp v) = -cexp (x + y + u + v) from
      fun x y u v => by rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring,
    show ∀ x y : ℂ, -cexp x * cexp y = -cexp (x + y) from fun x y => by rw [Complex.exp_add]; ring]
  congr 2
  push_cast
  field_simp
  ring

theorem sprod_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    sprod N (r + N) s τ = -(qa N r s τ)⁻¹ * sprod N r s τ := by
  have hq := norm_qq_lt_one hτ
  set q := qq τ with hqdef
  set w := qa N r s τ with hwdef
  have hq0 : q ≠ 0 := qq_ne_zero τ
  have hw0 : w ≠ 0 := qa_ne_zero N r s τ
  unfold sprod
  simp only [qa_add_level_left N hN, ← hqdef, ← hwdef]

  have ht : ∀ n : ℕ, (1 - q ^ (n + 1) * (q * w)) * (1 - q ^ (n + 1) * (q * w)⁻¹)
      = (1 - q ^ (n + 1 + 1) * w) * (1 - q ^ n * w⁻¹) := by
    intro n
    rw [mul_inv, pow_succ q (n + 1), pow_succ q n]
    field_simp
  rw [tprod_congr ht]

  have hA2 : Multipliable fun n : ℕ => 1 - q ^ (n + 1 + 1) * w := by
    simpa [add_assoc] using multipliable_one_sub_pow_mul hq w 2
  have hA1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w := multipliable_one_sub_pow_mul hq w 1
  have hB1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w⁻¹ := multipliable_one_sub_pow_mul hq w⁻¹ 1
  have hB0 : Multipliable fun n : ℕ => 1 - q ^ n * w⁻¹ := by
    simpa using multipliable_one_sub_pow_mul hq w⁻¹ 0

  rw [hA2.tprod_mul hB0, hA1.tprod_mul hB1,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ (n + 1) * w) hA2,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ n * w⁻¹) hB1]
  simp only [zero_add, pow_one, pow_zero, one_mul]
  field_simp
  ring

end SiegelPerE96

open SiegelPerE96 in

theorem solution (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine ⟨fun z => ?_, fun τ => ?_⟩ <;> simp [SiegelPerE96.siegelFun_level_zero]
  refine ⟨fun z => ?_, fun τ => ?_⟩
  · rw [SiegelPerE96.siegelFun_eq, SiegelPerE96.siegelFun_eq, SiegelPerE96.pref_add_level N hN,
      SiegelPerE96.sprod_add_level N hN, mul_assoc]
  · rw [SiegelPerE96.siegelFun_eq, SiegelPerE96.siegelFun_eq, SiegelPerE96.pref_add_level_left N hN,
      SiegelPerE96.sprod_add_level_left N hN r s τ.2]
    have hw : SiegelPerE96.qa N r s (τ : ℂ) ≠ 0 := SiegelPerE96.qa_ne_zero N r s τ
    field_simp

end

end S_ModularCurve_SiegelUnit_siegelFun_add_level
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_siegelFun_add_level (solution)
