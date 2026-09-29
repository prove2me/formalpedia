-- Prove2me | solution 1 for Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/42466c89-17a2-519f-9366-86941801ece6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative

set_option autoImplicit false

open Polynomial

namespace P2MHI

variable {W : Type*} [CommRing W] (I : Ideal W)

theorem smod_iff (n : ℕ) (x y : W) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule W W)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem isUnit_add_of_mem [IsAdicComplete I W] {v a : W} (hv : IsUnit v) (ha : a ∈ I) : IsUnit (v + a) := by
  have hj := IsAdicComplete.le_jacobson_bot I ha
  rw [Ideal.mem_jacobson_bot] at hj
  obtain ⟨w, rfl⟩ := hv
  have h1 : IsUnit (a * (↑w⁻¹ : W) + 1) := hj _
  have : (↑w : W) + a = ↑w * (a * ↑w⁻¹ + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (↑w : W) a, mul_assoc, Units.mul_inv, mul_one, add_comm]
  rw [this]
  exact (Units.isUnit w).mul h1

section Newton

variable (G : Polynomial W) (y₀ u : W)

def step (y : W) : W := y - u * G.eval y

def seq : ℕ → W
  | 0 => y₀
  | k + 1 => step G u (seq k)

variable {G y₀ u}

theorem seq_succ (k : ℕ) : seq G y₀ u (k + 1) = seq G y₀ u k - u * G.eval (seq G y₀ u k) := rfl

theorem seq_spec (hu : (Polynomial.derivative G).eval y₀ * u = 1) (hG : G.eval y₀ ∈ I) :
    ∀ k, seq G y₀ u k - y₀ ∈ I ∧ G.eval (seq G y₀ u k) ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => exact ⟨by simp [seq], by simpa [seq] using hG⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set y := seq G y₀ u k with hy
    have hstep : seq G y₀ u (k + 1) = y + (-(u * G.eval y)) := by rw [seq_succ, sub_eq_add_neg]
    constructor
    · rw [hstep, add_sub_right_comm]
      exact I.add_mem h1 (I.neg_mem (I.mul_mem_left _ (Ideal.pow_le_self (Nat.succ_ne_zero k) h2)))
    · rw [hstep]
      obtain ⟨c, hc⟩ := Polynomial.binomExpansion G y (-(u * G.eval y))
      rw [hc]

      obtain ⟨z, hz⟩ := Polynomial.evalSubFactor (Polynomial.derivative G) y₀ y
      have hdiff : (Polynomial.derivative G).eval y₀ - (Polynomial.derivative G).eval y ∈ I := by
        rw [hz]; exact I.mul_mem_left _ (by rw [← neg_sub]; exact I.neg_mem h1)
      have hkey : G.eval y + (Polynomial.derivative G).eval y * -(u * G.eval y)
          = G.eval y * (((Polynomial.derivative G).eval y₀ - (Polynomial.derivative G).eval y) * u) := by
        have := hu
        linear_combination (-(G.eval y)) * this
      rw [hkey]
      refine (I ^ (k + 1 + 1)).add_mem ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul h2 (I.mul_mem_right _ hdiff)
      · have : c * (-(u * G.eval y)) ^ 2 = (c * u ^ 2) * (G.eval y * G.eval y) := by ring
        rw [this, pow_succ]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul h2 (Ideal.pow_le_self (Nat.succ_ne_zero k) h2))

theorem seq_succ_sub_mem (hu : (Polynomial.derivative G).eval y₀ * u = 1) (hG : G.eval y₀ ∈ I) (k : ℕ) :
    seq G y₀ u (k + 1) - seq G y₀ u k ∈ I ^ (k + 1) := by
  rw [seq_succ, sub_sub_cancel_left]
  exact (I ^ (k + 1)).neg_mem (Ideal.mul_mem_left _ _ ((seq_spec I hu hG k).2))

theorem seq_cauchy (hu : (Polynomial.derivative G).eval y₀ * u = 1) (hG : G.eval y₀ ∈ I) {m n : ℕ} (hmn : m ≤ n) :
    seq G y₀ u n - seq G y₀ u m ∈ I ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have : seq G y₀ u (n + 1) - seq G y₀ u m = (seq G y₀ u (n + 1) - seq G y₀ u n) + (seq G y₀ u n - seq G y₀ u m) := by ring
    rw [this]
    exact (I ^ m).add_mem (Ideal.pow_le_pow_right (by omega) (seq_succ_sub_mem I hu hG n)) ih

end Newton

theorem main [IsAdicComplete I W] (G : Polynomial W) (y₀ : W) (hG : G.eval y₀ ∈ I)
    (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
    ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0 := by
  obtain ⟨uu, huu⟩ := hG'
  set u : W := ↑uu⁻¹ with hu
  have hu1 : (Polynomial.derivative G).eval y₀ * u = 1 := by rw [← huu, hu, Units.mul_inv]

  have hcauchy : ∀ {m n : ℕ}, m ≤ n → seq G y₀ u m ≡ seq G y₀ u n [SMOD (I ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [smod_iff, ← neg_sub]
    exact (I ^ m).neg_mem (seq_cauchy I hu1 hG hmn)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (seq G y₀ u) hcauchy
  have hL' : ∀ n, seq G y₀ u n - L ∈ I ^ n := fun n => (smod_iff I n _ _).mp (hL n)
  have hroot : G.eval L = 0 := by
    refine IsHausdorff.haus' (I := I) (G.eval L) fun n => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨z, hz⟩ := Polynomial.evalSubFactor G L (seq G y₀ u n)
    have : G.eval L = (G.eval L - G.eval (seq G y₀ u n)) + G.eval (seq G y₀ u n) := by ring
    rw [this, hz]
    refine (I ^ n).add_mem ?_ ?_
    · exact Ideal.mul_mem_left _ _ (by rw [← neg_sub]; exact (I ^ n).neg_mem (hL' n))
    · exact Ideal.pow_le_pow_right (Nat.le_succ n) ((seq_spec I hu1 hG n).2)
  have hcong : L - y₀ ∈ I := by
    have h1 : seq G y₀ u 1 - L ∈ I ^ 1 := hL' 1
    rw [pow_one] at h1
    have h2 := (seq_spec I hu1 hG 1).1
    have : L - y₀ = (seq G y₀ u 1 - y₀) - (seq G y₀ u 1 - L) := by ring
    rw [this]; exact I.sub_mem h2 h1
  refine ⟨L, ⟨hcong, hroot⟩, ?_⟩

  rintro y ⟨hy1, hy2⟩
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion G L (y - L)
  rw [add_sub_cancel, hy2, hroot, zero_add] at hc

  have hfac : (y - L) * ((Polynomial.derivative G).eval L + c * (y - L)) = 0 := by
    have := hc; linear_combination -this
  have hyL : y - L ∈ I := by
    have : y - L = (y - y₀) - (L - y₀) := by ring
    rw [this]; exact I.sub_mem hy1 hcong
  have hunit : IsUnit ((Polynomial.derivative G).eval L + c * (y - L)) := by
    obtain ⟨z, hz⟩ := Polynomial.evalSubFactor (Polynomial.derivative G) L y₀
    have : (Polynomial.derivative G).eval L + c * (y - L)
        = (Polynomial.derivative G).eval y₀ + (z * (L - y₀) + c * (y - L)) := by
      have := hz; linear_combination this
    rw [this]
    exact isUnit_add_of_mem I ⟨uu, huu⟩ (I.add_mem (I.mul_mem_left _ hcong) (I.mul_mem_left _ hyL))
  have hzero : y - L = 0 := by
    rw [mul_comm] at hfac
    exact (hunit.mul_right_eq_zero).mp hfac
  exact (sub_eq_zero.mp hzero)

end P2MHI

theorem solution
    {W : Type*} [CommRing W] (I : Ideal W) [IsAdicComplete I W]
    (G : Polynomial W) (y₀ : W) (hG : G.eval y₀ ∈ I)
    (hG' : IsUnit ((Polynomial.derivative G).eval y₀)) :
    ∃! y : W, y - y₀ ∈ I ∧ G.eval y = 0 :=
  P2MHI.main I G y₀ hG hG'

end S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative
end P2MW
export P2MW.S_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative (solution)
