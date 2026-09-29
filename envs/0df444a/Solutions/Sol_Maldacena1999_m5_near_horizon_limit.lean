-- Prove2me | solution 1 for Maldacena1999.m5_near_horizon_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:33:26.706869+00:00
-- url     : https://prove2.me/submissions/64fd70b7-5b93-4fe2-a352-ce3c833d0eee

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
    (ω : EuclideanSpace ℝ (Fin 5)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 6 → ℝ) (δω : EuclideanSpace ℝ (Fin 5)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (Real.pi * N) ^ (1 / 3 : ℝ) * minkowskiForm 5 δx +
        4 * (Real.pi * N) ^ (2 / 3 : ℝ) * δU ^ 2 / U ^ 2 +
        (Real.pi * N) ^ (2 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  have hc : 0 < Real.pi * (N : ℝ) := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hU0 : U ≠ 0 := hU.ne'
  have hC : 0 < Real.pi * (N : ℝ) / U ^ 6 := by positivity
  have hT1 := malda_tendsto_rpow (-(1/3:ℝ)) 6 (by norm_num) _ hC
  have hT2 := malda_tendsto_rpow (2/3:ℝ) 6 (by norm_num) _ hC
  have hT := (hT1.mul_const (minkowskiForm 5 δx)).add
    (hT2.mul_const (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2))
  have hval : (Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) * minkowskiForm 5 δx +
      (Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) * (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2) =
      U ^ 2 / (Real.pi * N) ^ (1 / 3 : ℝ) * minkowskiForm 5 δx +
        4 * (Real.pi * N) ^ (2 / 3 : ℝ) * δU ^ 2 / U ^ 2 +
        (Real.pi * N) ^ (2 / 3 : ℝ) * ‖δω‖ ^ 2 := by
    rw [Real.div_rpow hc.le (pow_nonneg hU.le 6), Real.div_rpow hc.le (pow_nonneg hU.le 6),
      malda_pow_rpow_neg U hU.le 6 2 (-(1/3)) (by norm_num),
      malda_pow_rpow_nat U hU.le 6 4 (2/3) (by norm_num), Real.rpow_neg hc.le]
    have h1 : 0 < (Real.pi * (N : ℝ)) ^ (1/3:ℝ) := Real.rpow_pos_of_pos hc _
    generalize (Real.pi * (N : ℝ)) ^ (1/3:ℝ) = a at h1 ⊢
    generalize (Real.pi * (N : ℝ)) ^ (2/3:ℝ) = b
    field_simp
    try ring
  have hev : (fun lp : ℝ => (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) * minkowskiForm 5 δx +
      (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) * (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with lp hlp
    have hlp : 0 < lp := hlp
    have hlp0 : lp ≠ 0 := hlp.ne'
    have hH : 0 < lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6 := by positivity
    have hf : m5HarmonicFn N lp (U ^ 2 * lp ^ 3) =
        (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) / (lp ^ 2) ^ 3 := by
      unfold m5HarmonicFn
      field_simp
      try ring
    unfold m5Metric
    rw [hf, Real.div_rpow hH.le (by positivity : (0:ℝ) ≤ (lp ^ 2) ^ 3),
      Real.div_rpow hH.le (by positivity : (0:ℝ) ≤ (lp ^ 2) ^ 3),
      malda_pow_rpow_neg (lp ^ 2) (by positivity) 3 1 (-(1/3)) (by norm_num),
      malda_pow_rpow_nat (lp ^ 2) (by positivity) 3 2 (2/3) (by norm_num)]
    generalize (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) = A
    generalize (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) = B
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev
