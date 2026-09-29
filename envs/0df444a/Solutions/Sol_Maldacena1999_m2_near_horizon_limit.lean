-- Prove2me | solution 1 for Maldacena1999.m2_near_horizon_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:44:26.39389+00:00
-- url     : https://prove2.me/submissions/99202751-58ba-41f6-95a5-4afd627293df

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

lemma malda_tendsto_rpow (a : ℝ) (k : ℕ) (hk : k ≠ 0) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun t : ℝ => (t ^ k + C) ^ a) (𝓝[>] 0) (𝓝 (C ^ a)) := by
  have hcont : Continuous (fun t : ℝ => t ^ k + C) := by fun_prop
  have h1 : Tendsto (fun t : ℝ => t ^ k + C) (𝓝 0) (𝓝 C) := by
    have := hcont.tendsto 0
    simpa [zero_pow hk] using this
  exact (h1.rpow_const (Or.inl hC.ne')).mono_left nhdsWithin_le_nhds

lemma malda_pow_rpow_nat (y : ℝ) (hy : 0 ≤ y) (n m : ℕ) (a : ℝ) (h : (n : ℝ) * a = m) :
    (y ^ n) ^ a = y ^ m := by
  rw [← Real.rpow_natCast_mul hy, h, Real.rpow_natCast]

lemma malda_pow_rpow_neg (y : ℝ) (hy : 0 ≤ y) (n m : ℕ) (a : ℝ) (h : (n : ℝ) * a = -m) :
    (y ^ n) ^ a = (y ^ m)⁻¹ := by
  rw [← Real.rpow_natCast_mul hy, h, Real.rpow_neg hy, Real.rpow_natCast]

open Maldacena1999 Filter Topology in
theorem solution (N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 8)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 3 → ℝ) (δω : EuclideanSpace ℝ (Fin 8)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
        (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (2 ^ 5 * Real.pi ^ 2 * N) ^ (2 / 3 : ℝ) * minkowskiForm 2 δx +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) / 4 * δU ^ 2 / U ^ 2 +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  have hK : 0 < 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hU0 : U ≠ 0 := hU.ne'
  have hC : 0 < 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3 := by positivity
  have hT1 := malda_tendsto_rpow (-(2/3:ℝ)) 3 (by norm_num) _ hC
  have hT2 := malda_tendsto_rpow (1/3:ℝ) 3 (by norm_num) _ hC
  have hT := (hT1.mul_const (minkowskiForm 2 δx)).add
    (hT2.mul_const (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2))
  have hval : (2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) * minkowskiForm 2 δx +
      (2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) * (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2) =
      U ^ 2 / (2 ^ 5 * Real.pi ^ 2 * N) ^ (2 / 3 : ℝ) * minkowskiForm 2 δx +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) / 4 * δU ^ 2 / U ^ 2 +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) * ‖δω‖ ^ 2 := by
    rw [Real.div_rpow hK.le (pow_nonneg hU.le 3), Real.div_rpow hK.le (pow_nonneg hU.le 3),
      malda_pow_rpow_neg U hU.le 3 2 (-(2/3)) (by norm_num),
      malda_pow_rpow_nat U hU.le 3 1 (1/3) (by norm_num), Real.rpow_neg hK.le]
    have h1 : 0 < (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (2/3:ℝ) := Real.rpow_pos_of_pos hK _
    generalize (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (2/3:ℝ) = a at h1 ⊢
    generalize (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/3:ℝ) = b
    field_simp
    try ring
  have hev : (fun lp : ℝ => (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) *
      minkowskiForm 2 δx + (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) *
      (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
        (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with lp hlp
    have hlp : 0 < lp := hlp
    have hlp0 : lp ≠ 0 := hlp.ne'
    have hH : 0 < lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3 := by positivity
    have hs2 : Real.sqrt (U * lp ^ 3) ^ 2 = U * lp ^ 3 := Real.sq_sqrt (by positivity)
    have hf : m2HarmonicFn N lp (Real.sqrt (U * lp ^ 3)) =
        (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) / lp ^ 3 := by
      unfold m2HarmonicFn
      rw [show Real.sqrt (U * lp ^ 3) ^ 6 = (Real.sqrt (U * lp ^ 3) ^ 2) ^ 3 by ring, hs2]
      field_simp
      try ring
    unfold m2Metric
    rw [hf, Real.div_rpow hH.le (pow_nonneg hlp.le 3), Real.div_rpow hH.le (pow_nonneg hlp.le 3),
      malda_pow_rpow_neg lp hlp.le 3 2 (-(2/3)) (by norm_num),
      malda_pow_rpow_nat lp hlp.le 3 1 (1/3) (by norm_num)]
    simp only [mul_pow, div_pow, hs2]
    generalize (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) = A
    generalize (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) = B
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev
