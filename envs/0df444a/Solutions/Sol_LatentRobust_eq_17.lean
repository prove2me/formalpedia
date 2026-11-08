-- Prove2me | solution 1 for LatentRobust.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:43:23.230717+00:00
-- url     : https://prove2.me/submissions/4169dea2-6b0f-4933-b477-f27a135d5382

import Mathlib
import Definitions.Def_LatentRobust_lpNorm

open LatentRobust in
theorem solution {d : ℕ} (p εp : ℝ) (hp : 2 ≤ p) (x : Fin d → ℝ) :
    {x' : Fin d → ℝ | lpNorm p (x' - x) ≤ εp} ⊆
      {x' : Fin d → ℝ | lpNorm 2 (x' - x) ≤ εp * (d : ℝ) ^ ((1 : ℝ) / 2 - 1 / p)} := by
  intro x' hx'
  simp only [Set.mem_setOf_eq] at hx' ⊢
  unfold LatentRobust.lpNorm at hx' ⊢
  set v := x' - x
  have hp0 : 0 < p := by linarith
  have hB0 : 0 ≤ ∑ i, |v i| ^ p := Finset.sum_nonneg (fun i _ => by positivity)
  have hA0 : 0 ≤ ∑ i, |v i| ^ (2:ℝ) := Finset.sum_nonneg (fun i _ => by positivity)
  have hε : 0 ≤ εp := le_trans (Real.rpow_nonneg hB0 _) hx'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero] at hx' ⊢
    rw [Real.zero_rpow (by norm_num)]
    exact mul_nonneg hε (Real.rpow_nonneg le_rfl _)
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  -- power mean with weights 1/d and exponent p/2
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ)
    (fun _ => 1 / (d:ℝ)) (fun i => |v i| ^ (2:ℝ)) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    (fun i _ => by positivity) (p := p / 2) (by linarith)
  have hz : ∀ i, (|v i| ^ (2:ℝ)) ^ (p / 2) = |v i| ^ p := by
    intro i
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  simp only [hz] at hpm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hpm
  -- take 1/p powers
  have hmono := Real.rpow_le_rpow (by positivity) hpm (by positivity : (0:ℝ) ≤ 1 / p)
  rw [← Real.rpow_mul (by positivity), show p / 2 * (1 / p) = 1 / 2 by field_simp,
    Real.mul_rpow (by positivity) hA0, Real.mul_rpow (by positivity) hB0] at hmono
  -- hmono : (1/d)^(1/2) * A^(1/2) ≤ (1/d)^(1/p) * B^(1/p)
  have hd2 : (0:ℝ) < (1 / (d:ℝ)) ^ ((1:ℝ) / 2) := by positivity
  have key : (∑ i, |v i| ^ (2:ℝ)) ^ ((1:ℝ) / 2) ≤
      (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) * (∑ i, |v i| ^ p) ^ (1 / p) := by
    have e : (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) =
        (1 / (d:ℝ)) ^ (1 / p) / (1 / (d:ℝ)) ^ ((1:ℝ) / 2) := by
      rw [Real.div_rpow zero_le_one hdr.le, Real.div_rpow zero_le_one hdr.le, Real.one_rpow,
        Real.one_rpow, Real.rpow_sub hdr]
      field_simp
    rw [e, div_mul_eq_mul_div, le_div_iff₀ hd2]
    linarith [mul_comm ((1 / (d:ℝ)) ^ ((1:ℝ) / 2)) ((∑ i, |v i| ^ (2:ℝ)) ^ ((1:ℝ) / 2))]
  have hdp : 0 ≤ (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) := Real.rpow_nonneg hdr.le _
  calc (∑ i, |v i| ^ (2:ℝ)) ^ ((1:ℝ) / 2)
      ≤ (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) * (∑ i, |v i| ^ p) ^ (1 / p) := key
    _ ≤ (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) * εp := mul_le_mul_of_nonneg_left hx' hdp
    _ = εp * (d:ℝ) ^ ((1:ℝ) / 2 - 1 / p) := mul_comm _ _
