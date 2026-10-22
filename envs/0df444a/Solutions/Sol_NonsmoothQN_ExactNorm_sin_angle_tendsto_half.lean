-- Prove2me | solution 1 for NonsmoothQN.ExactNorm.sin_angle_tendsto_half
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:31:32.748452+00:00
-- url     : https://prove2.me/submissions/710f643b-5751-4810-b630-dafa7935236f

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

set_option autoImplicit false
open Matrix Filter Topology NonsmoothQN.ExactNorm

theorem nqe_inv_sqrt2_le : 1 / Real.sqrt 2 ≤ 23 / 32 := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_iff₀ hp]
  have : (32 / 23 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  nlinarith

theorem nqe_lip (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / Real.sqrt 2))
    (hy : y ∈ Set.Icc (0 : ℝ) (1 / Real.sqrt 2)) :
    |angleMap x - angleMap y| ≤ (2 / 3) * |x - y| := by
  have h23 := nqe_inv_sqrt2_le
  have hx1 : x ≤ 23 / 32 := hx.2.trans h23
  have hy1 : y ≤ 23 / 32 := hy.2.trans h23
  unfold angleMap
  set u := Real.sqrt ((1 - x) / 2) with hu
  set v := Real.sqrt ((1 - y) / 2) with hv
  have hu2 : u ^ 2 = (1 - x) / 2 := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = (1 - y) / 2 := Real.sq_sqrt (by linarith)
  have hu3 : 3 / 8 ≤ u := Real.le_sqrt_of_sq_le (by nlinarith)
  have hv3 : 3 / 8 ≤ v := Real.le_sqrt_of_sq_le (by nlinarith)
  have h1 : |u - v| * (u + v) = |x - y| / 2 := by
    have : (u - v) * (u + v) = (y - x) / 2 := by nlinarith
    calc |u - v| * (u + v) = |(u - v) * (u + v)| := by
          rw [abs_mul, abs_of_pos (by linarith : 0 < u + v)]
      _ = |x - y| / 2 := by
          rw [this, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_sub_comm]
  nlinarith [mul_le_mul_of_nonneg_left (show (3/4:ℝ) ≤ u + v by linarith) (abs_nonneg (u - v)), h1, abs_nonneg (x - y)]

theorem solution :
    angleMap '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / Real.sqrt 2) ∧
      (∃ K : NNReal, K < 1 ∧ LipschitzOnWith K angleMap (Set.Icc 0 (1 / Real.sqrt 2))) ∧
      ∀ s : ℕ → ℝ, s 0 ∈ Set.Icc (0 : ℝ) 1 → (∀ k, s (k + 1) = angleMap (s k)) →
        Tendsto s atTop (𝓝 (1 / 2)) := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have himg : angleMap '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / Real.sqrt 2) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      unfold angleMap
      refine ⟨Real.sqrt_nonneg _, ?_⟩
      rw [one_div, ← Real.sqrt_inv, show ((2 : ℝ))⁻¹ = (2 : ℝ)⁻¹ from rfl]
      apply Real.sqrt_le_sqrt
      linarith [hs.1, hs.2]
    · rintro ⟨ht0, ht1⟩
      have ht2 : t ^ 2 ≤ 1 / 2 := by
        have : t * Real.sqrt 2 ≤ 1 := by
          rwa [le_div_iff₀ hp] at ht1
        nlinarith [mul_nonneg ht0 hp.le]
      refine ⟨1 - 2 * t ^ 2, ⟨by linarith, by nlinarith [sq_nonneg t]⟩, ?_⟩
      unfold angleMap
      rw [show (1 - (1 - 2 * t ^ 2)) / 2 = t ^ 2 by ring, Real.sqrt_sq ht0]
  have hK : (((2 / 3 : NNReal)) : ℝ) = 2 / 3 := by norm_num
  refine ⟨himg, ⟨(2 / 3 : NNReal), by rw [← NNReal.coe_lt_coe, hK]; norm_num, ?_⟩, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [hK]
    simpa [Real.dist_eq] using nqe_lip x y hx hy
  · intro s h0 hs
    have h1le : 1 / Real.sqrt 2 ≤ 1 := nqe_inv_sqrt2_le.trans (by norm_num)
    have hIcc : ∀ k, s k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih =>
        have := Set.mem_image_of_mem angleMap ih
        rw [himg] at this
        rw [hs k]
        exact ⟨this.1, this.2.trans h1le⟩
    have hmem : ∀ k, s (k + 1) ∈ Set.Icc (0 : ℝ) (1 / Real.sqrt 2) := by
      intro k
      have := Set.mem_image_of_mem angleMap (hIcc k)
      rw [himg] at this
      rwa [hs k]
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / Real.sqrt 2) := by
      refine ⟨by norm_num, ?_⟩
      rw [le_div_iff₀ hp]
      nlinarith
    have hfix : angleMap (1 / 2) = 1 / 2 := by
      unfold angleMap
      rw [show (1 - 1 / 2 : ℝ) / 2 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hbound : ∀ k, |s (k + 1) - 1 / 2| ≤ (2 / 3) ^ k * |s 1 - 1 / 2| := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h := nqe_lip (s (k + 1)) (1 / 2) (hmem k) hhalf
        rw [← hs (k + 1), hfix] at h
        calc |s (k + 1 + 1) - 1 / 2| ≤ 2 / 3 * |s (k + 1) - 1 / 2| := h
          _ ≤ 2 / 3 * ((2 / 3) ^ k * |s 1 - 1 / 2|) := by gcongr
          _ = (2 / 3) ^ (k + 1) * |s 1 - 1 / 2| := by ring
    have hlim : Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k * |s 1 - 1 / 2|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 / 3 : ℝ) < 1)).mul_const (|s 1 - 1 / 2|)
    have hs1 : Tendsto (fun k : ℕ => s (k + 1)) atTop (𝓝 (1 / 2)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg) (fun k => by simpa [Real.dist_eq] using hbound k) hlim
    exact (tendsto_add_atTop_iff_nat 1).mp hs1
