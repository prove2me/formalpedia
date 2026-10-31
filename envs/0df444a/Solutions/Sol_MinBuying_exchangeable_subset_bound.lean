-- Prove2me | solution 1 for MinBuying.exchangeable_subset_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:37:17.806222+00:00
-- url     : https://prove2.me/submissions/2a2c9c54-600b-415d-b97d-631b5938d4ca

import Mathlib

open scoped BigOperators

namespace MinBuyingSubsetProof

private lemma choose_difference_bound (m q n : ℕ) (hmn : m ≤ n) :
    n.choose (q+1) ≤ m.choose (q+1) + (n-m) * (n-1).choose q := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Nat.choose_succ_succ]
    have hmono := Nat.choose_le_choose q (Nat.sub_le n 1)
    have hmul := Nat.mul_le_mul_left (n-m) hmono
    have hsub : n+1-m = n-m+1 := by omega
    rw [hsub]
    simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one]
    nlinarith only [ih,hmul]

private lemma choose_fraction_bound (n i k : ℕ) (hi : i < n) (hk : 2 ≤ k)
    (hbudget : 2*k*(n-i) ≤ n) :
    (k+1) * n.choose k ≤ 2*n*i.choose (k-1) := by
  have hn : 2 ≤ n := by nlinarith [Nat.sub_pos_of_lt hi]
  have hkm : k-1+1=k := by omega
  have hkm2 : k-2+1=k-1 := by omega
  have hnm : n-1+1=n := by omega
  have hnm2 : n-2+1=n-1 := by omega
  have hie : i ≤ n-1 := by omega
  have hbound := choose_difference_bound i (k-2) (n-1) hie
  rw [hkm2,show n-1-1=n-2 by omega] at hbound
  have hcn : n * (n-1).choose (k-1) = n.choose k * k := by
    have h := Nat.add_one_mul_choose_eq (n-1) (k-1)
    simpa only [hnm,hkm] using h
  have hcn1 : (n-1)*(n-2).choose (k-2) = (n-1).choose (k-1)*(k-1) := by
    have h := Nat.add_one_mul_choose_eq (n-2) (k-2)
    simpa only [hnm2,hkm2] using h
  have he : n-i = n-1-i+1 := by omega
  have hsmall : 2*k*(n-1-i) ≤ n-1 := by rw [he] at hbudget; nlinarith
  have hcsmall := Nat.mul_le_mul_right ((n-2).choose (k-2)) hsmall
  rw [hcn1] at hcsmall
  have hbound' := Nat.mul_le_mul_left (2*k) hbound
  have hrel : (k-1)*(n-1).choose (k-1)+(n-1).choose (k-1) = k*(n-1).choose (k-1) := by
    rw [← add_one_mul,hkm]
  have hkey : (k+1)*(n-1).choose (k-1) ≤ 2*k*i.choose (k-1) := by
    nlinarith only [hcsmall,hbound',hrel]
  have hscaled : k*((k+1)*n.choose k) ≤ k*(2*n*i.choose (k-1)) := by
    calc
      k*((k+1)*n.choose k) = (k+1)*(n*((n-1).choose (k-1))) := by
        simp only [hcn]
        ring
      _ = n*((k+1)*(n-1).choose (k-1)) := by ring
      _ ≤ n*(2*k*i.choose (k-1)) := Nat.mul_le_mul_left n hkey
      _ = k*(2*n*i.choose (k-1)) := by ring
  exact (mul_le_mul_iff_right₀ (show 0 < k by omega)).mp hscaled

end MinBuyingSubsetProof

/-- The explicit subset probability in the proof of Theorem 3, with zero-based item index. -/
theorem solution (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    let k := max 1 (n / (2*(n-i)))
    1 / (4*((n-i : ℕ) : ℝ)) ≤ (i.choose (k-1) : ℝ) / (n.choose k : ℝ) := by
  let k := max 1 (n / (2*(n-i)))
  have hd : 0 < n-i := Nat.sub_pos_of_lt hi
  have hk : 1 ≤ k := le_max_left _ _
  have hkn : k ≤ n := max_le hn (Nat.div_le_self _ _)
  have hfloor : n < 2*(n-i)*(k+1) := by
    have hdiv : n / (2*(n-i)) < k+1 := by exact Nat.lt_succ_of_le (le_max_right _ _)
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*(n-i))).mp hdiv
  change 1 / (4*((n-i : ℕ) : ℝ)) ≤ (i.choose (k-1) : ℝ) / (n.choose k : ℝ)
  by_cases hk1 : k=1
  · rw [hk1]
    simp only [Nat.sub_self,Nat.choose_zero_right,Nat.cast_one,Nat.choose_one_right]
    apply one_div_le_one_div_of_le (by positivity)
    have hn4 : n ≤ 4*(n-i) := by rw [hk1] at hfloor; nlinarith only [hfloor]
    exact_mod_cast hn4
  · have hk2 : 2 ≤ k := by omega
    have hkdef : k=n/(2*(n-i)) := by dsimp [k] at hk1 ⊢;omega
    have hbudget : 2*k*(n-i) ≤ n := by
      rw [hkdef]
      have h := Nat.div_mul_le_self n (2*(n-i))
      nlinarith only [h]
    have hc := MinBuyingSubsetProof.choose_fraction_bound n i k hi hk2 hbudget
    have hchoose : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn
    have hD : 0 < (n-i : ℕ) := hd
    apply (div_le_div_iff₀ (by positivity) hchoose).mpr
    have hcR : ((k:ℝ)+1)*(n.choose k : ℝ) ≤ 2*(n:ℝ)*(i.choose (k-1) : ℝ) := by exact_mod_cast hc
    have hfR : (n:ℝ) < 2*((n-i:ℕ):ℝ)*((k:ℝ)+1) := by exact_mod_cast hfloor
    have hmul := mul_le_mul_of_nonneg_right hfR.le (show 0 ≤ (i.choose (k-1) : ℝ) by positivity)
    have hK : 0 < (k:ℝ)+1 := by positivity
    nlinarith only [hcR,hmul,hK]
