-- Prove2me | solution 1 for MaxMinFracSched.eq_11_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:53:18.625459+00:00
-- url     : https://prove2.me/submissions/e4eb2b0f-8358-4a7c-a742-3a06501c62e5

import Mathlib
import Definitions.Def_MaxMinFracSched_tt
import Definitions.Def_MaxMinFracSched_Dtot

open MaxMinFracSched in
theorem solution (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    MaxMinFracSched.Dtot x k 1 = x ^ (k - 1) ∧
    ∀ i : ℕ, 2 ≤ i → i ≤ k →
      MaxMinFracSched.Dtot x k i = MaxMinFracSched.tt x k i * (1 - x ^ 2) / x ^ (i - 1) := by
  have hx0' : x ≠ 0 := hx0.ne'
  have htel : ∀ p, ∑ ℓ ∈ Finset.Icc 1 p, MaxMinFracSched.TT x k ℓ = MaxMinFracSched.tt x k p := by
    intro p
    induction p with
    | zero => simp [MaxMinFracSched.tt]
    | succ p ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      unfold MaxMinFracSched.TT
      simp only [Nat.add_sub_cancel]
      ring
  have hgeo : ∀ n, ∑ m ∈ Finset.range n, (1 - x) / x ^ (m + 1) = 1 / x ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp <;> ring
  constructor
  · unfold MaxMinFracSched.Dtot
    rw [Finset.sum_range_one]
    unfold MaxMinFracSched.hw
    rw [if_pos rfl]
    unfold MaxMinFracSched.TT MaxMinFracSched.tt
    simp
  · intro i hi2 hik
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
    unfold MaxMinFracSched.Dtot
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have h0 : MaxMinFracSched.hw x k 0 (n + 2) = MaxMinFracSched.TT x k (n + 2) := by
      unfold MaxMinFracSched.hw; rw [if_pos rfl]
    have hlast : MaxMinFracSched.hw x k (n + 1) (n + 2) =
        (1 - x) / x ^ (n + 1) * MaxMinFracSched.tt x k (n + 2) := by
      unfold MaxMinFracSched.hw
      rw [if_neg (by omega), if_pos rfl, htel]
    have hmid : ∀ m ∈ Finset.range n, MaxMinFracSched.hw x k (m + 1) (n + 2) =
        (1 - x) / x ^ (m + 1) * MaxMinFracSched.TT x k (n + 2) := by
      intro m hm
      rw [Finset.mem_range] at hm
      unfold MaxMinFracSched.hw
      rw [if_neg (by omega), if_neg (by omega)]
    rw [Finset.sum_congr rfl hmid, ← Finset.sum_mul, hgeo, h0, hlast]
    obtain ⟨e, he⟩ : ∃ e, e = k - (n + 2) := ⟨_, rfl⟩
    have htt2 : MaxMinFracSched.tt x k (n + 2) = x ^ e := by
      unfold MaxMinFracSched.tt; rw [if_neg (by omega), he]
    have htt1 : MaxMinFracSched.tt x k (n + 1) = x ^ (e + 1) := by
      unfold MaxMinFracSched.tt; rw [if_neg (by omega)]; congr 1; omega
    have hTT : MaxMinFracSched.TT x k (n + 2) = x ^ e - x ^ (e + 1) := by
      unfold MaxMinFracSched.TT
      rw [show n + 2 - 1 = n + 1 by omega, htt2, htt1]
    rw [hTT, htt2, show n + 2 - 1 = n + 1 by omega, pow_succ x n, pow_succ x e]
    field_simp <;> ring
