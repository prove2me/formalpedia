-- Prove2me | solution 1 for HeckeTreeWalk.cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4d203e06-1cb2-5d0f-ad96-3610f40db772

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow

set_option autoImplicit false

namespace HeckeTreeWalkAux

theorem walk_eq_zero_of_lt (q : ℕ) (W : ℕ → ℕ → ℕ) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k d : ℕ, k < d → W k d = 0 := by
  intro k
  induction k with
  | zero =>
    intro d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    exact h0s d'
  | succ k ih =>
    intro d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [hstep, ih d' (by omega), ih (d' + 2) (by omega), mul_zero, add_zero]

theorem telescope (q : ℤ) (A : ℕ → ℤ) : ∀ n : ℕ,
    (q + 1) * A 0 + ∑ r ∈ Finset.range (n + 1), (A r + q * A (r + 1)) * (q ^ (r + 1) - q ^ r) =
      2 * q * (A 0 + ∑ r ∈ Finset.range n, A (r + 1) * (q ^ (r + 1) - q ^ r)) +
        q * A (n + 1) * (q ^ (n + 1) - q ^ n) := by
  intro n
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, Finset.sum_range_succ]
    ring

theorem sum_shift_split (q : ℤ) (B C : ℕ → ℤ) (μ : ℕ) :
    ∑ r ∈ Finset.range μ, (B r + q * C r) * (q ^ (r + 1) - q ^ r) =
      ∑ r ∈ Finset.range μ, B r * (q ^ (r + 1) - q ^ r) + q * ∑ r ∈ Finset.range μ, C r * (q ^ (r + 1) - q ^ r) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem main (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k : ℕ, ∀ d μ : ℕ, d + 2 * μ = k →
      (W k d : ℤ) + ∑ r ∈ Finset.range μ, (W k (d + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) =
        ((k.choose μ : ℕ) : ℤ) * (q : ℤ) ^ μ := by
  have hvan := walk_eq_zero_of_lt q W h0s hstep
  intro k
  induction k with
  | zero =>
    intro d μ h
    have hμ : μ = 0 := by omega
    have hd : d = 0 := by omega
    subst hμ hd
    simp [h00]
  | succ k ih =>
    intro d μ h
    rcases d with _ | d'
    ·
      obtain ⟨μ', rfl⟩ : ∃ μ' : ℕ, μ = μ' + 1 := ⟨μ - 1, by omega⟩
      have hk : k = 2 * μ' + 1 := by omega
      have e0 : (W (k + 1) 0 : ℤ) = ((q : ℤ) + 1) * W k 1 := by rw [hroot]; push_cast; ring
      have e2 : ∀ r : ℕ, (W (k + 1) (0 + 2 * (r + 1)) : ℤ) =
          (W k (2 * r + 1) : ℤ) + (q : ℤ) * W k (2 * (r + 1) + 1) := by
        intro r
        rw [show 0 + 2 * (r + 1) = (2 * r + 1) + 1 by ring, hstep, show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by ring]
        push_cast
        ring
      rw [e0, Finset.sum_congr rfl (fun r _ => by rw [e2 r])]
      have hT := telescope (q : ℤ) (fun r => (W k (2 * r + 1) : ℤ)) μ'
      simp only [Nat.mul_zero, zero_add] at hT
      rw [hT, hvan k (2 * (μ' + 1) + 1) (by omega)]
      have hih := ih 1 μ' (by omega)
      have hre : ∀ r : ℕ, (1 + 2 * (r + 1)) = 2 * (r + 1) + 1 := fun r => by ring
      simp only [hre] at hih
      rw [hih, hk]
      rw [show 2 * μ' + 1 + 1 = (2 * μ' + 1) + 1 by rfl, Nat.choose_succ_succ', Nat.choose_symm_half]
      push_cast
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring
    ·
      have hk : d' + 2 * μ = k := by omega
      have e1 : (W (k + 1) (d' + 1) : ℤ) = (W k d' : ℤ) + (q : ℤ) * W k (d' + 2) := by
        rw [hstep]; push_cast; ring
      have e2 : ∀ r : ℕ, (W (k + 1) (d' + 1 + 2 * (r + 1)) : ℤ) =
          (W k (d' + 2 * (r + 1)) : ℤ) + (q : ℤ) * W k (d' + 2 + 2 * (r + 1)) := by
        intro r
        rw [show d' + 1 + 2 * (r + 1) = (d' + 2 * (r + 1)) + 1 by ring, hstep,
          show d' + 2 * (r + 1) + 2 = d' + 2 + 2 * (r + 1) by ring]
        push_cast; ring
      rw [e1, Finset.sum_congr rfl (fun r _ => by rw [e2 r]), sum_shift_split]
      have hA := ih d' μ hk
      rcases μ with _ | μ'
      · have hA' : (W k d' : ℤ) = 1 := by simpa using hA
        simp [hvan k (d' + 2) (by omega), hA']
      · have hB := ih (d' + 2) μ' (by omega)
        rw [Finset.sum_range_succ (fun r => (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)),
          hvan k (d' + 2 + 2 * (μ' + 1)) (by omega)]
        have hre : ∀ r : ℕ, d' + 2 + 2 * (r + 1) = d' + 2 * (r + 1) + 2 := fun r => by ring

        have : (W k d' : ℤ) + (q : ℤ) * W k (d' + 2) +
            (∑ r ∈ Finset.range (μ' + 1), (W k (d' + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) +
              (q : ℤ) * (∑ r ∈ Finset.range μ', (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) +
                ((0 : ℕ) : ℤ) * ((q : ℤ) ^ (μ' + 1) - (q : ℤ) ^ μ'))) =
            ((W k d' : ℤ) + ∑ r ∈ Finset.range (μ' + 1), (W k (d' + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)) +
              (q : ℤ) * ((W k (d' + 2) : ℤ) +
                ∑ r ∈ Finset.range μ', (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)) := by
          push_cast; ring
        rw [this, hA, hB, Nat.choose_succ_succ']
        push_cast
        ring

end HeckeTreeWalkAux

theorem solution
    (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2))
    (d μ : ℕ) :
    (W (d + 2 * μ) d : ℤ) +
        ∑ r ∈ Finset.range μ, (W (d + 2 * μ) (d + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) =
      (((d + 2 * μ).choose μ : ℕ) : ℤ) * (q : ℤ) ^ μ :=
  HeckeTreeWalkAux.main q W h00 h0s hroot hstep (d + 2 * μ) d μ rfl

end S_HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow
end P2MW
export P2MW.S_HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow (solution)
