-- Prove2me | solution 1 for OAI.SingleFold.Packed.update_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:17:27.185495+00:00
-- url     : https://prove2.me/submissions/4b8f5a76-5852-445b-87ce-6f16d9a6fd29

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed
theorem h49_low (B s : ℕ) (f : ℕ → ℕ) (hf : ∀ t < s, f t < B) :
    ∑ t ∈ Finset.range s, f t * B^t < B^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun t ht => hf t (by omega))
    have h2 := hf s (by omega)
    have : f s * B^s ≤ (B - 1) * B^s := Nat.mul_le_mul_right _ (by omega)
    have h3 : (B - 1) * B^s + B^s = B^s * B := by
      rcases B with _ | B
      · omega
      · simp only [Nat.add_sub_cancel]; ring
    omega

theorem h49_split (B s m : ℕ) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range (s+1+m), f t * B^t =
      ∑ t ∈ Finset.range s, f t * B^t +
        B^s * (f s + B * ∑ t ∈ Finset.range m, f (s+1+t) * B^t) := by
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.mul_sum, mul_add, Finset.mul_sum]
  have : ∀ t ∈ Finset.range m, f (s+1+t) * B^(s+1+t) = B^s * (B * (f (s+1+t) * B^t)) := by
    intro t _; rw [pow_add, pow_add]; ring
  rw [Finset.sum_congr rfl this]; ring

theorem h49_digit (B s m : ℕ) (f : ℕ → ℕ) (hf : ∀ t ≤ s, f t < B) :
    (∑ t ∈ Finset.range (s+1+m), f t * B^t) / B^s % B = f s := by
  rw [h49_split]
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf s le_rfl)
  have hl := h49_low B s f (fun t ht => hf t ht.le)
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf s le_rfl)]

def h49_shift (c0 : ℕ) (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => c0
  | t+1 => u t

theorem h49_shift_sum (B T c0 : ℕ) (u : ℕ → ℕ) :
    ∑ t ∈ Finset.range (T+1), h49_shift c0 u t * B^t =
      c0 + B * ∑ t ∈ Finset.range T, u t * B^t := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [h49_shift, pow_zero, mul_one, pow_succ]
  rw [add_comm]; congr 1
  apply Finset.sum_congr rfl; intro t _; ring

theorem solution {B T m d : ℕ} (hB : 2*m ≤ B) (hd : d < m)
    (r a f : ℕ → ℕ) (hr : ∀t < T+1,r t < m) (ha : ∀t < T,a t ≤ 1) (hf : ∀t < T,f t ≤ 1)
    (he : pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a)) :
    r 0=d ∧ ∀t < T,r (t+1)+f t=r t+a t := by
  have hL : pack B (T+1) r + B * pack B T f =
      ∑ t ∈ Finset.range (T+1), h49_shift (r 0) (fun t => r (t+1) + f t) t * B^t := by
    rw [h49_shift_sum]; unfold pack
    rw [Finset.sum_range_succ', Finset.mul_sum, Finset.mul_sum]
    have hh : ∀ i ∈ Finset.range T, B * ((r (i+1) + f i) * B^i) =
        r (i+1) * B^(i+1) + B * (f i * B^i) := by intro i _; ring
    rw [Finset.sum_congr rfl hh, Finset.sum_add_distrib]; ring
  have hR : d + B * (pack B T r + pack B T a) =
      ∑ t ∈ Finset.range (T+1), h49_shift d (fun t => r t + a t) t * B^t := by
    rw [h49_shift_sum]; unfold pack
    rw [← Finset.sum_add_distrib]
    congr 2; apply Finset.sum_congr rfl; intro t _; ring
  rw [hL, hR] at he
  have hdig : ∀ s ≤ T, h49_shift (r 0) (fun t => r (t+1) + f t) s =
      h49_shift d (fun t => r t + a t) s := by
    intro s hs
    have e1 := h49_digit B s (T - s) (h49_shift (r 0) (fun t => r (t+1) + f t)) (by
      intro t ht
      rcases t with _ | t
      · simp only [h49_shift]; have := hr 0 (by omega); omega
      · simp only [h49_shift]; have := hr (t+1) (by omega); have := hf t (by omega); omega)
    have e2 := h49_digit B s (T - s) (h49_shift d (fun t => r t + a t)) (by
      intro t ht
      rcases t with _ | t
      · simp only [h49_shift]; omega
      · simp only [h49_shift]; have := hr t (by omega); have := ha t (by omega); omega)
    rw [show s + 1 + (T - s) = T + 1 by omega] at e1 e2
    rw [← e1, ← e2, he]
  refine ⟨hdig 0 (by omega), fun t ht => hdig (t+1) (by omega)⟩

