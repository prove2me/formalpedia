-- Prove2me | solution 1 for HeckeTreeWalk.two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fd8bcaa6-8f50-5b2c-b36d-f50d2b31a68b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow

set_option autoImplicit false

open Finset

namespace HeckeTreeWalkWeightedShellMoment

variable {R : Type*} [CommRing R]

def W (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (q + 1) * W q k 1
  | k + 1, d + 1 => W q k d + q * W q k (d + 2)

variable (q : R)

@[scoped simp] theorem W_zero_zero : W q 0 0 = 1 := rfl
@[scoped simp] theorem W_zero_succ (d : ℕ) : W q 0 (d + 1) = 0 := rfl
theorem W_succ_zero (k : ℕ) : W q (k + 1) 0 = (q + 1) * W q k 1 := rfl
theorem W_succ_succ (k d : ℕ) : W q (k + 1) (d + 1) = W q k d + q * W q k (d + 2) := rfl

theorem W_eq_zero_of_lt : ∀ k d : ℕ, k < d → W q k d = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, d + 1, h => by
      rw [W_succ_succ, W_eq_zero_of_lt k d (by omega), W_eq_zero_of_lt k (d + 2) (by omega)]
      simp

def bal (k j : ℕ) : R :=
  (k.choose j : R) - if j = 0 then 0 else (k.choose (j - 1) : R)

@[scoped simp] theorem bal_zero (k : ℕ) : (bal k 0 : R) = 1 := by simp [bal]

theorem bal_succ (k j : ℕ) : (bal k (j + 1) : R) = (k.choose (j + 1) : R) - (k.choose j : R) := by
  simp [bal]

theorem bal_succ_succ (k j : ℕ) : (bal (k + 1) (j + 1) : R) = bal k (j + 1) + bal k j := by
  rcases j with _ | j
  · simp [bal_succ, bal_zero, Nat.choose_succ_succ]
  · rw [bal_succ, bal_succ, bal_succ, Nat.choose_succ_succ k (j + 1), Nat.choose_succ_succ k j]
    push_cast
    ring

theorem bal_odd_half (i : ℕ) : (bal (2 * i + 1) (i + 1) : R) = 0 := by
  rw [bal_succ, Nat.choose_symm_half, sub_self]

theorem sum_bal (k : ℕ) : ∀ J : ℕ, ∑ j ∈ range (J + 1), (bal k j : R) = (k.choose J : R)
  | 0 => by simp
  | J + 1 => by rw [sum_range_succ, sum_bal k J, bal_succ]; ring

theorem sum_sub_mul_bal (k : ℕ) :
    ∀ J : ℕ, ∑ j ∈ range (J + 1), ((J : R) - j) * bal k j = ∑ i ∈ range J, (k.choose i : R)
  | 0 => by simp
  | J + 1 => by
      have h : ∑ j ∈ range (J + 1 + 1), (((J + 1 : ℕ) : R) - j) * bal k j
          = ∑ j ∈ range (J + 1), ((J : R) - j) * bal k j + ∑ j ∈ range (J + 1), (bal k j : R) := by
        rw [sum_range_succ, ← sum_add_distrib]
        have : (((J + 1 : ℕ) : R) - ((J + 1 : ℕ) : R)) * bal k (J + 1) = 0 := by ring
        rw [this, add_zero]
        refine sum_congr rfl fun j _ => ?_
        push_cast; ring
      rw [h, sum_sub_mul_bal k J, sum_bal, sum_range_succ]

def P (k i : ℕ) : R := ∑ j ∈ range (i + 1), (bal k j : R) * q ^ j

theorem P_zero (k : ℕ) : P q k 0 = 1 := by simp [P]

theorem P_succ (k i : ℕ) : P q k (i + 1) = P q k i + bal k (i + 1) * q ^ (i + 1) := by
  simp [P, sum_range_succ]

theorem P_step (k : ℕ) : ∀ i : ℕ, P q k (i + 1) + q * P q k i = P q (k + 1) (i + 1)
  | 0 => by
      rw [P_succ, P_zero, P_succ, P_zero, bal_succ, bal_succ]
      simp
      ring
  | i + 1 => by
      rw [P_succ q k (i + 1), P_succ q (k + 1) (i + 1), bal_succ_succ k (i + 1)]
      have := P_step k i
      linear_combination this + q * P_succ q k i

theorem P_step_zero (k : ℕ) : P q k 0 + q * 0 = P q (k + 1) 0 := by simp [P_zero]

theorem P_boundary (i : ℕ) : (q + 1) * P q (2 * i + 1) i = P q (2 * i + 2) (i + 1) := by
  have h := P_step q (2 * i + 1) i
  rw [P_succ, bal_odd_half, zero_mul, add_zero] at h
  linear_combination h

theorem W_pos_eq : ∀ k d i : ℕ, k = d + 1 + 2 * i → W q k (d + 1) = P q k i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d i hk
    rcases k with _ | k
    · omega
    rw [W_succ_succ]
    rcases d with _ | d
    ·
      rcases i with _ | i
      · have hk0 : k = 0 := by omega
        subst hk0
        simp [P_zero, W_eq_zero_of_lt]
      · have hk' : k = 2 * i + 2 := by omega
        subst hk'
        rw [show 2 * i + 2 = (2 * i + 1) + 1 from rfl, W_succ_zero]
        rw [ih (2 * i + 1) (by omega) 0 i (by ring)]
        rw [show (2 : ℕ) = 1 + 1 from rfl, ih (2 * i + 1 + 1) (by omega) 1 i (by ring)]
        rw [P_boundary, show 2 * i + 1 + 1 = 2 * i + 2 from rfl]
        rw [show 2 * i + 2 + 1 = (2 * i + 2) + 1 from rfl, ← P_step q (2 * i + 2) i]
    ·
      have hk' : k = d + 1 + 2 * i := by omega
      rw [ih k (by omega) d i hk']
      rcases i with _ | i
      · rw [W_eq_zero_of_lt q k (d + 3) (by omega)]
        exact P_step_zero q k
      · rw [show d + 3 = (d + 2) + 1 from rfl, ih k (by omega) (d + 2) i (by omega)]
        exact P_step q k i

theorem W_base_eq (n : ℕ) : W q (2 * n + 2) 0 = P q (2 * n + 2) (n + 1) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, W_succ_zero,
    W_pos_eq q (2 * n + 1) 0 n (by ring), P_boundary]

theorem delta_eq (n m : ℕ) (hm : m ≤ n) :
    q ^ m * (W q (2 * n) (2 * m) - W q (2 * n) (2 * m + 2)) = bal (2 * n) (n - m) * q ^ n := by
  rcases m with _ | m
  · rcases n with _ | n
    · simp [W_eq_zero_of_lt]
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring, W_base_eq,
        show 2 * 0 + 2 = 1 + 1 from rfl, W_pos_eq q (2 * n + 2) 1 n (by ring), P_succ]
      simp
  · obtain ⟨t, rfl⟩ : ∃ t, n = m + 1 + t := ⟨n - (m + 1), by omega⟩
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
      W_pos_eq q (2 * (m + 1 + t)) (2 * m + 1) t (by ring)]
    rcases t with _ | t
    · rw [W_eq_zero_of_lt q _ _ (by omega), sub_zero]
      simp [P_zero]
    · rw [show 2 * m + 1 + 1 + 2 = (2 * m + 3) + 1 by ring,
        W_pos_eq q (2 * (m + 1 + (t + 1))) (2 * m + 3) t (by ring), P_succ]
      rw [show m + 1 + (t + 1) - (m + 1) = t + 1 from by omega]
      ring

def moment (k n : ℕ) : R := ∑ m ∈ range (n + 1), q ^ m * (W q k (2 * m) - W q k (2 * m + 2))

def weightedMoment (k n : ℕ) : R :=
  ∑ m ∈ range (n + 1), (m : R) * (q ^ m * (W q k (2 * m) - W q k (2 * m + 2)))

theorem moment_eq (n : ℕ) : moment q (2 * n) n = ((2 * n).choose n : R) * q ^ n := by
  unfold moment
  rw [sum_congr rfl fun m hm => delta_eq q n m (by simpa [Nat.lt_succ_iff] using hm), ← sum_mul,
    ← sum_bal (2 * n) n]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  congr 1
  have := mem_range.1 hj
  omega

theorem weightedMoment_eq (n : ℕ) :
    weightedMoment q (2 * n) n = (∑ J ∈ range n, ((2 * n).choose J : R)) * q ^ n := by
  unfold weightedMoment
  rw [sum_congr rfl fun m hm => by rw [delta_eq q n m (by simpa [Nat.lt_succ_iff] using hm)]]
  simp_rw [← mul_assoc]
  rw [← sum_mul, ← sum_sub_mul_bal (2 * n) n, ← sum_range_reflect]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  rw [show n + 1 - 1 - j = n - j from by omega, Nat.sub_sub_self (show j ≤ n by omega)]
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring

theorem two_mul_sum_range_choose_add_choose_middle (n : ℕ) :
    2 * ∑ J ∈ range n, (2 * n).choose J + (2 * n).choose n = 4 ^ n := by
  rcases n with _ | m
  · simp
  ·
    have hrow : ∀ J, (2 * (m + 1)).choose (J + 1)
        = (2 * m + 1).choose J + (2 * m + 1).choose (J + 1) := by
      intro J; rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ]
    have h1 : ∑ J ∈ range (m + 1), (2 * (m + 1)).choose J
        = 1 + ∑ J ∈ range m, ((2 * m + 1).choose J + (2 * m + 1).choose (J + 1)) := by
      rw [sum_range_succ']
      simp [hrow, add_comm]
    have h2 : (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1).choose m := by
      rw [hrow m, Nat.choose_symm_half]; ring
    have hh := Nat.sum_range_choose_halfway m
    have h3 : ∑ J ∈ range m, (2 * m + 1).choose (J + 1) = 4 ^ m - 1 := by
      have := (sum_range_succ' (fun J => (2 * m + 1).choose J) m)
      rw [hh] at this
      simp at this
      omega
    have h4 : ∑ J ∈ range m, (2 * m + 1).choose J = 4 ^ m - (2 * m + 1).choose m := by
      have := sum_range_succ (fun J => (2 * m + 1).choose J) m
      rw [hh] at this
      omega
    have h5 : (2 * m + 1).choose m ≤ 4 ^ m := Nat.choose_middle_le_pow m
    have h6 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    rw [h1, h2, sum_add_distrib, h3, h4, pow_succ]
    omega

theorem two_mul_weightedMoment_eq (n : ℕ) :
    2 * weightedMoment q (2 * n) n = (4 : R) ^ n * q ^ n - ((2 * n).choose n : R) * q ^ n := by
  rw [weightedMoment_eq]
  have h := congrArg (fun x : ℕ => (x : R)) (two_mul_sum_range_choose_add_choose_middle n)
  push_cast at h
  linear_combination (q ^ n) * h

theorem abel_shell (f : ℕ → R) : ∀ n : ℕ,
    ∑ m ∈ range (n + 1), q ^ m * (f m - f (m + 1))
      = f 0 + ∑ r ∈ Icc 1 n, f r * (q ^ r - q ^ (r - 1)) - q ^ n * f (n + 1)
  | 0 => by simp
  | n + 1 => by
      rw [sum_range_succ, abel_shell f n, sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        Nat.add_sub_cancel]
      ring

theorem abel_shell_weighted (f : ℕ → R) : ∀ n : ℕ,
    ∑ m ∈ range (n + 1), (m : R) * (q ^ m * (f m - f (m + 1)))
      = ∑ r ∈ Icc 1 n, (r : R) * f r * (q ^ r - q ^ (r - 1))
          + ∑ r ∈ Icc 1 n, f r * q ^ (r - 1) - (n : R) * q ^ n * f (n + 1)
  | 0 => by simp
  | n + 1 => by
      rw [sum_range_succ, abel_shell_weighted f n, sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]
      push_cast
      ring

theorem shell_sub_eq_mul (f : ℕ → R) : ∀ n : ℕ,
    ∑ r ∈ Icc 1 n, f r * (q ^ r - q ^ (r - 1)) = (q - 1) * ∑ r ∈ Icc 1 n, f r * q ^ (r - 1)
  | 0 => by simp
  | n + 1 => by
      rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        shell_sub_eq_mul f n, Nat.add_sub_cancel]
      ring

theorem shell_weighted_eq (n : ℕ) :
    2 * ((q - 1) * ∑ r ∈ Icc 1 n, (r : R) * W q (2 * n) (2 * r) * (q ^ r - q ^ (r - 1))
        - W q (2 * n) 0)
      = (q - 1) * (4 * q) ^ n - (q + 1) * ((2 * n).choose n : R) * q ^ n := by

  set f : ℕ → R := fun m => W q (2 * n) (2 * m) with hf
  have htop : f (n + 1) = 0 := W_eq_zero_of_lt q (2 * n) (2 * (n + 1)) (by omega)
  have hre : ∀ m : ℕ, W q (2 * n) (2 * m + 2) = f (m + 1) := fun m => rfl
  have hf0 : W q (2 * n) 0 = f 0 := rfl
  have hfr : ∀ r : ℕ, W q (2 * n) (2 * r) = f r := fun r => rfl

  have hE := moment_eq q n
  have hD := two_mul_weightedMoment_eq q n
  unfold moment at hE
  unfold weightedMoment at hD
  simp only [hre, hfr] at hE hD

  rw [abel_shell q f n, htop, mul_zero, sub_zero] at hE
  rw [abel_shell_weighted q f n, htop, mul_zero, sub_zero] at hD
  have hS := shell_sub_eq_mul q f n
  simp only [hfr, hf0]
  rw [mul_pow]
  linear_combination (-2) * hE + (q - 1) * hD + 2 * hS

theorem cast_eq_W (q : ℕ) (V : ℕ → ℕ → ℕ) (h00 : V 0 0 = 1) (h0s : ∀ d : ℕ, V 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, V (k + 1) 0 = (q + 1) * V k 1)
    (hstep : ∀ k d : ℕ, V (k + 1) (d + 1) = V k d + q * V k (d + 2)) :
    ∀ k d : ℕ, (V k d : ℤ) = W (q : ℤ) k d := by
  intro k
  induction k with
  | zero =>
      intro d
      rcases d with _ | d
      · simp [h00]
      · simp [h0s]
  | succ k ih =>
      intro d
      rcases d with _ | d
      · rw [hroot, W_succ_zero, ← ih 1]
        push_cast
        ring
      · rw [hstep, W_succ_succ, ← ih d, ← ih (d + 2)]
        push_cast
        ring

end HeckeTreeWalkWeightedShellMoment
p2m_reactivate "P2MW.S_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow.HeckeTreeWalkWeightedShellMoment"

open HeckeTreeWalkWeightedShellMoment in
theorem solution
    (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k : ℕ, 2 * (((q : ℤ) - 1) *
          ∑ r ∈ Finset.Icc 1 k, (r : ℤ) * (W (2 * k) (2 * r) : ℤ) * ((q : ℤ) ^ r - (q : ℤ) ^ (r - 1)) -
        (W (2 * k) 0 : ℤ)) =
      ((q : ℤ) - 1) * (4 * (q : ℤ)) ^ k - ((q : ℤ) + 1) * ((2 * k).choose k : ℤ) * (q : ℤ) ^ k := by
  intro k
  have hc := cast_eq_W q W h00 h0s hroot hstep
  simp only [hc]
  exact shell_weighted_eq (q : ℤ) k

end S_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
end P2MW
export P2MW.S_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow (solution)
