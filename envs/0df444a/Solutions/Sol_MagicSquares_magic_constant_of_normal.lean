-- Prove2me | solution 1 for MagicSquares.magic_constant_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T13:35:59.227599+00:00
-- url     : https://prove2.me/submissions/8a6fb7d6-1d64-4e2d-a37f-414d499ee8bd

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares
open scoped BigOperators

/-- Twice the sum of `1, …, m` is `m (m+1)`. -/
lemma two_mul_sum_Icc_sol (m : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 m, k) = m * (m + 1) := by
  have hset : Finset.Icc 1 m = (Finset.range (m + 1)).erase 0 := by
    ext k
    simp [Finset.mem_Icc]
    omega
  rw [hset]
  have h0 : 0 ∈ Finset.range (m + 1) := by simp
  have hs : (∑ k ∈ (Finset.range (m + 1)).erase 0, k) + 0 =
      ∑ k ∈ Finset.range (m + 1), k := by
    simpa using (Finset.sum_erase_add (s := Finset.range (m + 1)) (a := 0)
      (f := fun k : ℕ => k) h0)
  have hsame : (∑ k ∈ (Finset.range (m + 1)).erase 0, k) =
      ∑ k ∈ Finset.range (m + 1), k := by
    simpa using hs
  rw [hsame]
  have h := Finset.sum_range_id_mul_two (m + 1)
  have h' : (∑ k ∈ Finset.range (m + 1), k) * 2 = (m + 1) * m := by
    simpa using h
  calc
    2 * (∑ k ∈ Finset.range (m + 1), k) = (∑ k ∈ Finset.range (m + 1), k) * 2 := by ring
    _ = (m + 1) * m := h'
    _ = m * (m + 1) := by ring

/-- Solution for `MagicSquares.magic_constant_of_normal`.

Summing the `n` rows gives `totalSum M = n * s`. On the other hand `IsNormal M`
says the index-to-entry map is a bijection onto `{1, …, n²}`, so `totalSum M` is
the sum of `1, …, n²`, i.e. `n²(n²+1)/2`. Hence `2 n s = n²(n²+1) = n · n(n²+1)`,
and cancelling the positive factor `n` gives `2 s = n (n²+1)`. The degenerate
case `n = 0` is handled separately: there `diagSum M = 0`, so `s = 0`. -/
theorem solution (n : ℕ) (M : Square n ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    2 * s = n * (n ^ 2 + 1) := by
  classical
  have hT : totalSum M = n * s := by
    calc
      totalSum M = ∑ i : Fin n, rowSum M i := by simp [totalSum, rowSum]
      _ = ∑ i : Fin n, s := by simp [hM.1.1]
      _ = n * s := by simp
  let f : Fin n × Fin n → ℕ := fun p => M p.1 p.2
  have hf_inj : Function.Injective f := hN.2
  have himg : (Finset.univ.image f) = Finset.Icc 1 (n ^ 2) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, _hp, rfl⟩
      exact Finset.mem_Icc.mpr (hN.1 p)
    · have hc1 : (Finset.univ.image f).card = n ^ 2 := by
        rw [Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n × Fin n))) hf_inj]
        simp [Fintype.card_prod, pow_two]
      have hc2 : (Finset.Icc 1 (n ^ 2)).card = n ^ 2 := by
        simp
      rw [hc1, hc2]
  have hsum_image : (∑ x ∈ Finset.univ.image f, x) = ∑ p : Fin n × Fin n, f p := by
    exact Finset.sum_image (by
      intro x _hx y _hy hxy
      exact hf_inj hxy)
  have hprod : (∑ p : Fin n × Fin n, f p) = ∑ i : Fin n, ∑ j : Fin n, M i j := by
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  have hT2 : totalSum M = ∑ k ∈ Finset.Icc 1 (n ^ 2), k := by
    calc
      totalSum M = ∑ i : Fin n, ∑ j : Fin n, M i j := by rfl
      _ = ∑ p : Fin n × Fin n, f p := hprod.symm
      _ = ∑ x ∈ Finset.univ.image f, x := by rw [← hsum_image]
      _ = ∑ k ∈ Finset.Icc 1 (n ^ 2), k := by rw [himg]
  have hmain : 2 * (n * s) = n ^ 2 * (n ^ 2 + 1) := by
    calc
      2 * (n * s) = 2 * totalSum M := by rw [hT]
      _ = 2 * (∑ k ∈ Finset.Icc 1 (n ^ 2), k) := by rw [hT2]
      _ = n ^ 2 * (n ^ 2 + 1) := two_mul_sum_Icc_sol (n ^ 2)
  cases n with
  | zero =>
      have hs0 : s = 0 := by
        have hd := hM.2.1
        simpa [diagSum] using hd.symm
      simp [hs0]
  | succ n' =>
      have hcancel : (n' + 1) * (2 * s) =
          (n' + 1) * ((n' + 1) * ((n' + 1) ^ 2 + 1)) := by
        calc
          (n' + 1) * (2 * s) = 2 * ((n' + 1) * s) := by ring
          _ = (n' + 1) ^ 2 * ((n' + 1) ^ 2 + 1) := hmain
          _ = (n' + 1) * ((n' + 1) * ((n' + 1) ^ 2 + 1)) := by ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n') hcancel
