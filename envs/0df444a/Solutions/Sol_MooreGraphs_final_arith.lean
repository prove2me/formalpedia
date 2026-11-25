-- Prove2me | solution 1 for MooreGraphs.final_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:20:11.96812+00:00
-- url     : https://prove2.me/submissions/472ce8e7-1493-4a09-bc0b-fac22abad597

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (d : ℤ) (h : (d : ℝ) * √(4 * k - 3) = k ^ 2 - 2 * k) :
    k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  rcases eq_or_ne d 0 with rfl | hd
  · left
    have h0 : ((k : ℝ) - 2) * k = 0 := by simp at h; linarith
    have hk' : (k : ℝ) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h0).resolve_right hk'
    exact_mod_cast (by linarith : (k : ℝ) = 2)
  · right
    have hcast : ((4 * k - 3 : ℕ) : ℝ) = 4 * k - 3 := by
      push_cast [show 3 ≤ 4 * k by omega]; ring
    have hrat : ¬ Irrational √((4 * k - 3 : ℕ) : ℝ) := by
      rw [hcast]
      intro hirr
      have : √(4 * (k : ℝ) - 3) = ((((k : ℚ) ^ 2 - 2 * k) / d : ℚ) : ℝ) := by
        push_cast
        rw [eq_div_iff (by exact_mod_cast hd)]
        linarith
      exact hirr ⟨_, this.symm⟩
    rw [irrational_sqrt_natCast_iff, not_not] at hrat
    obtain ⟨t, ht⟩ := hrat
    rw [← hcast, ht] at h
    push_cast at h
    rw [Real.sqrt_mul_self (by positivity)] at h
    have hz : d * t = (k : ℤ) ^ 2 - 2 * k := by exact_mod_cast h
    have h4 : (4 * k : ℤ) = t * t + 3 := by omega
    have hdvd : (t : ℤ) ∣ 15 :=
      ⟨t ^ 3 - 2 * t - 16 * d, by linear_combination 16 * hz + (4 * k + t ^ 2 - 5) * h4⟩
    have hdvd' : t ∈ Nat.divisors 15 := Nat.mem_divisors.2 ⟨by exact_mod_cast hdvd, by norm_num⟩
    have h15 : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [h15] at hdvd'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdvd'
    rcases hdvd' with rfl | rfl | rfl | rfl <;> omega
end MooreGraphs
