-- Prove2me | solution 1 for IntMul.HvdH.chunk_product
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:38:39.198988+00:00
-- url     : https://prove2.me/submissions/5866b4d4-3e36-484b-ab05-44926c00dbd1

import Mathlib

open Polynomial Finset

theorem chunk_sum (b : ℕ) : ∀ (N f : ℕ), f < 2 ^ (b * N) →
    f = ∑ j ∈ range N, f / 2 ^ (b * j) % 2 ^ b * 2 ^ (b * j) := by
  intro N
  induction N with
  | zero => intro f hf; simp at hf; simp [hf]
  | succ N ih =>
    intro f hf
    rw [sum_range_succ]
    have hr := ih (f % 2 ^ (b * N)) (Nat.mod_lt _ (by positivity))
    have hterm : ∀ j ∈ range N, f % 2 ^ (b * N) / 2 ^ (b * j) % 2 ^ b * 2 ^ (b * j)
        = f / 2 ^ (b * j) % 2 ^ b * 2 ^ (b * j) := by
      intro j hj
      simp at hj
      congr 1
      have e : 2 ^ (b * N) = 2 ^ (b * j) * 2 ^ (b * (N - j)) := by
        rw [← pow_add]; congr 1; rw [← mul_add]; congr 1; omega
      rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
      exact pow_dvd_pow 2 (by nlinarith [show 1 ≤ N - j by omega])
    rw [sum_congr rfl hterm] at hr
    have htop : f / 2 ^ (b * N) % 2 ^ b = f / 2 ^ (b * N) := by
      apply Nat.mod_eq_of_lt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      convert hf using 2; ring
    rw [htop, ← hr]
    have := Nat.mod_add_div f (2 ^ (b * N))
    linarith [mul_comm (2 ^ (b * N)) (f / 2 ^ (b * N))]

/-- the chunk polynomial `∑_{j<N} ⌊f / 2^{bj}⌋ mod 2^b · X^j` -/
noncomputable def chunkPoly (b N f : ℕ) : ℕ[X] :=
  ∑ j ∈ range N, C (f / 2 ^ (b * j) % 2 ^ b) * X ^ j

lemma chunkPoly_eval (b N f : ℕ) (hf : f < 2 ^ (b * N)) : (chunkPoly b N f).eval (2 ^ b) = f := by
  unfold chunkPoly
  rw [eval_finsetSum]
  conv_rhs => rw [chunk_sum b N f hf]
  refine sum_congr rfl fun j _ => ?_
  simp [pow_mul]

lemma chunkPoly_coeff (b N f k : ℕ) :
    (chunkPoly b N f).coeff k = if k < N then f / 2 ^ (b * k) % 2 ^ b else 0 := by
  unfold chunkPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp [h])]; simp
  · exact sum_eq_zero fun j hj => by simp at hj; simp; omega

theorem solution (b N f g : ℕ) (hN : 1 ≤ N) (hf : f < 2 ^ (b * N)) (hg : g < 2 ^ (b * N)) :
    f * g = ∑ j ∈ range (2 * N - 1),
        (∑ k ∈ range (j + 1),
          (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
          (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0)) * 2 ^ (b * j) ∧
    ∀ j, (∑ k ∈ range (j + 1),
          (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
          (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0)) < N * 2 ^ (2 * b) := by
  set H := chunkPoly b N f * chunkPoly b N g with hH
  have hcoeff : ∀ j, H.coeff j = ∑ k ∈ range (j + 1),
      (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
      (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0) := by
    intro j
    rw [hH, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [chunkPoly_coeff]
  constructor
  · have hdeg : ∀ j, 2 * N - 1 ≤ j → H.coeff j = 0 := by
      intro j hj
      rw [hcoeff]
      refine sum_eq_zero fun k hk => ?_
      simp at hk
      by_cases h1 : k < N
      · have : ¬ (j - k < N) := by omega
        simp [this]
      · simp [h1]
    have hnd : H.natDegree < 2 * N - 1 := by
      have : H.natDegree ≤ 2 * N - 2 :=
        (natDegree_le_iff_coeff_eq_zero).mpr fun j hj => hdeg j (by omega)
      omega
    have hev := eval_eq_sum_range' hnd (2 ^ b)
    rw [hH, eval_mul, chunkPoly_eval b N f hf, chunkPoly_eval b N g hg] at hev
    rw [hev]
    refine sum_congr rfl fun j _ => ?_
    rw [hcoeff, pow_mul]
  · intro j
    have hc : (2 ^ b - 1) * (2 ^ b - 1) < 2 ^ (2 * b) := by
      have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      have : 2 ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [two_mul, pow_add]
      rw [this]; exact Nat.mul_lt_mul'' (by omega) (by omega)
    have hterm : ∀ k ∈ range (j + 1),
        (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
        (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0)
          ≤ if k < N then (2 ^ b - 1) * (2 ^ b - 1) else 0 := by
      intro k _
      have m1 : ∀ x, x % 2 ^ b ≤ 2 ^ b - 1 := fun x => by
        have := Nat.mod_lt x (show 0 < 2 ^ b by positivity); omega
      split_ifs <;> simp_all [Nat.mul_le_mul]
    calc _ ≤ ∑ k ∈ range (j + 1), (if k < N then (2 ^ b - 1) * (2 ^ b - 1) else 0) :=
          sum_le_sum hterm
      _ ≤ ∑ k ∈ range N, (2 ^ b - 1) * (2 ^ b - 1) := by
          rw [← sum_filter]
          apply sum_le_sum_of_subset
          intro k hk; simp at hk ⊢; exact hk.2
      _ = N * ((2 ^ b - 1) * (2 ^ b - 1)) := by simp
      _ < N * 2 ^ (2 * b) := Nat.mul_lt_mul_of_pos_left hc (by omega)
