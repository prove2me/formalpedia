-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_coefficient_estimates_at_251
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:36:29.498927+00:00
-- url     : https://prove2.me/submissions/dacfdac9-0a36-4183-a7ef-962879cba38d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_head_coefficient_enclosures
import Theorems.Thm_GrothendieckLB_Supplement_cq_tail_weighted_square_bound

open GrothendieckLB GrothendieckLB.Supplement

private theorem reciprocal_sixth_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 2) ^ 6 ≤ 1 / (10 * x ^ 5) - 1 / (10 * (x + 2) ^ 5) := by
  have hp : 10 * x ^ 5 + x ^ 5 * (x + 2) ≤ (x + 2) ^ 6 := by
    have h : 0 ≤ 60 * x^4 + 160 * x^3 + 240 * x^2 + 192 * x + 64 := by positivity
    nlinarith only [h]
  apply (le_sub_iff_add_le).2
  apply sub_nonneg.mp
  have hden : x + 2 ≠ 0 := by positivity
  have hid :
      1 / (10 * x ^ 5) - (1 / (x + 2) ^ 6 + 1 / (10 * (x + 2) ^ 5)) =
        ((x + 2) ^ 6 - (10 * x ^ 5 + x ^ 5 * (x + 2))) / (10 * x ^ 5 * (x + 2) ^ 6) := by
    field_simp [hx.ne', hden] <;> ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hp) (by positivity)

private theorem reciprocal_sixth_sum (N : ℝ) (hN : 0 < N) (k : ℕ) :
    (∑ j ∈ Finset.range k, 1 / (N + 2 * ((j : ℝ) + 1)) ^ 6) ≤
      1 / (10 * N ^ 5) - 1 / (10 * (N + 2 * (k : ℝ)) ^ 5) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h := reciprocal_sixth_step (N + 2 * (k : ℝ)) (by positivity)
    rw [show N + 2 * (k : ℝ) + 2 = N + 2 * ((k : ℝ) + 1) by ring] at h
    linarith only [ih, h]

private theorem odd_tail_from_square_sums (a : ℕ → ℝ) (N B : ℝ) (hN : 0 < N) (hB : 0 ≤ B)
    (hw : ∀ k, (∑ j ∈ Finset.range k, (N + 2 * ((j : ℝ) + 1)) ^ 6 * (a j) ^ 2) ≤ B ^ 2) :
    Summable (fun j => |a j|) ∧ (∑' j, |a j|) ≤ B / Real.sqrt (10 * N ^ 5) := by
  let L (j : ℕ) : ℝ := N + 2 * ((j : ℝ) + 1)
  have hL (j : ℕ) : 0 < L j := by dsimp [L]; positivity
  have hbound (k : ℕ) : (∑ j ∈ Finset.range k, |a j|) ≤ B / Real.sqrt (10 * N ^ 5) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range k)
      (r := fun j => |a j|) (f := fun j => (L j)^6 * (a j)^2) (g := fun j => 1 / (L j)^6)
      (fun j _ => mul_nonneg (pow_nonneg (hL j).le _) (sq_nonneg _))
      (fun j _ => div_nonneg zero_le_one (pow_nonneg (hL j).le _))
      (fun j _ => by rw [sq_abs]; apply le_of_eq; field_simp [(hL j).ne'] <;> ring)
    have hrec : (∑ j ∈ Finset.range k, 1 / (L j)^6) ≤ 1 / (10 * N^5) :=
      (reciprocal_sixth_sum N hN k).trans (sub_le_self _ (by positivity))
    have hs : (∑ j ∈ Finset.range k, |a j|)^2 ≤ B^2 * (1/(10*N^5)) :=
      hcs.trans (mul_le_mul (hw k) hrec
        (Finset.sum_nonneg fun j _ => div_nonneg zero_le_one (pow_nonneg (hL j).le _))
        (sq_nonneg B))
    have hden : 0 ≤ 10 * N^5 := by positivity
    have hid : (B / Real.sqrt (10 * N^5))^2 = B^2 * (1/(10*N^5)) := by
      rw [div_pow, Real.sq_sqrt hden]
      ring
    rw [← hid] at hs
    exact (sq_le_sq₀ (Finset.sum_nonneg fun j _ => abs_nonneg (a j))
      (div_nonneg hB (Real.sqrt_nonneg _))).mp hs
  exact ⟨summable_of_sum_range_le (fun j => abs_nonneg (a j)) hbound,
    Real.tsum_le_of_sum_range_le (fun j => abs_nonneg (a j)) hbound⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem head_units_sum :
    (∑ j ∈ Finset.range 125, cqHeadUnits[j]?.getD 0) = 1132885992769046 := by
  decide +kernel

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    let b := fun m : ℕ => taylorCoeff m H
    0.881573822049 ≤ b 1 ∧
      (∑ j ∈ Finset.range 125, |b (2 * j + 3)|) ≤ 0.000011328860 ∧
      Summable (fun j : ℕ => |b (2 * j + 253)|) ∧
      (∑' j : ℕ, |b (2 * j + 253)|) ≤ 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let b (m : ℕ) := taylorCoeff m H
  obtain ⟨h1, hodd⟩ := cq_head_coefficient_enclosures
  refine ⟨le_trans (by norm_num : (0.881573822049 : ℝ) ≤ 88157382204959954858 / 10^20) h1, ?_, ?_⟩
  · calc
      (∑ j ∈ Finset.range 125, |b (2*j+3)|) ≤
          ∑ j ∈ Finset.range 125, ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10^20 :=
        Finset.sum_le_sum fun j hj => hodd j (Finset.mem_range.mp hj)
      _ = ((∑ j ∈ Finset.range 125, cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10^20 := by
        rw [← Finset.sum_div, Nat.cast_sum]
      _ ≤ 0.000011328860 := by rw [head_units_sum]; norm_num
  · exact odd_tail_from_square_sums (fun j => b (2*j+253)) 251 14.443
      (by norm_num) (by norm_num) cq_tail_weighted_square_bound
