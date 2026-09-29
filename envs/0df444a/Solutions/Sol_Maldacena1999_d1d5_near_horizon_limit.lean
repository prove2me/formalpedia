-- Prove2me | solution 1 for Maldacena1999.d1d5_near_horizon_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T13:04:29.010369+00:00
-- url     : https://prove2.me/submissions/5cec59c3-5092-47d0-93fd-ece265cfa6b5

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

open Maldacena1999 Filter Topology in
theorem solution (g v : ℝ) (hg : 0 < g) (hv : 0 < v)
    (Q1 Q5 : ℕ) (hQ1 : 0 < Q1) (hQ5 : 0 < Q5) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 4)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 2 → ℝ) (δω : EuclideanSpace ℝ (Fin 4)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α')
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) * minkowskiForm 1 δx +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * δU ^ 2 / U ^ 2 +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * ‖δω‖ ^ 2)) := by
  have hq1 : (0:ℝ) < Q1 := by exact_mod_cast hQ1
  have hq5 : (0:ℝ) < Q5 := by exact_mod_cast hQ5
  have hU0 : U ≠ 0 := hU.ne'
  have hv0 : v ≠ 0 := hv.ne'
  have hC1 : 0 < g * Q1 / (v * U ^ 2) := by positivity
  have hC5 : 0 < g * Q5 / U ^ 2 := by positivity
  have hT1a := (malda_tendsto_rpow (-(1/2:ℝ)) 1 one_ne_zero _ hC1).congr (fun t => by rw [pow_one])
  have hT5a := (malda_tendsto_rpow (-(1/2:ℝ)) 1 one_ne_zero _ hC5).congr (fun t => by rw [pow_one])
  have hT1b := (malda_tendsto_rpow (1/2:ℝ) 1 one_ne_zero _ hC1).congr (fun t => by rw [pow_one])
  have hT5b := (malda_tendsto_rpow (1/2:ℝ) 1 one_ne_zero _ hC5).congr (fun t => by rw [pow_one])
  have hT := ((hT1a.mul hT5a).mul_const (minkowskiForm 1 δx)).add
    ((hT1b.mul hT5b).mul_const (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2))
  have hG : 0 < g / Real.sqrt v * Real.sqrt (Q1 * Q5) := by
    have : 0 < Real.sqrt ((Q1:ℝ) * Q5) := Real.sqrt_pos.2 (by positivity)
    have : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
    positivity
  have hprod : Real.sqrt (g * Q1 / (v * U ^ 2)) * Real.sqrt (g * Q5 / U ^ 2) =
      g / Real.sqrt v * Real.sqrt (Q1 * Q5) / U ^ 2 := by
    rw [← Real.sqrt_mul hC1.le]
    have e : g * Q1 / (v * U ^ 2) * (g * Q5 / U ^ 2) =
        (g / Real.sqrt v * Real.sqrt (Q1 * Q5) / U ^ 2) ^ 2 := by
      rw [div_pow, mul_pow, div_pow, Real.sq_sqrt hv.le, Real.sq_sqrt (by positivity)]
      field_simp
      try ring
    rw [e, Real.sqrt_sq (by positivity)]
  have hval : (g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) * (g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) *
      minkowskiForm 1 δx + (g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) * (g * Q5 / U ^ 2) ^ (1/2:ℝ) *
      (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2) =
      U ^ 2 / (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) * minkowskiForm 1 δx +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * δU ^ 2 / U ^ 2 +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * ‖δω‖ ^ 2 := by
    rw [Real.rpow_neg hC1.le, Real.rpow_neg hC5.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← mul_inv, hprod]
    generalize g / Real.sqrt v * Real.sqrt (Q1 * Q5) = G at hG ⊢
    field_simp
    try ring
  have hev : (fun a : ℝ => (a + g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) *
      (a + g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) * minkowskiForm 1 δx +
      (a + g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) * (a + g * Q5 / U ^ 2) ^ (1/2:ℝ) *
      (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α') := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha : 0 < a := ha
    have ha0 : a ≠ 0 := ha.ne'
    have h1 : 0 < a + g * Q1 / (v * U ^ 2) := by positivity
    have h5 : 0 < a + g * Q5 / U ^ 2 := by positivity
    have hf1 : d1HarmonicFn g v Q1 a (a * U) = (a + g * Q1 / (v * U ^ 2)) / a := by
      unfold d1HarmonicFn
      field_simp
      try ring
    have hf5 : d5HarmonicFn g Q5 a (a * U) = (a + g * Q5 / U ^ 2) / a := by
      unfold d5HarmonicFn
      field_simp
      try ring
    unfold d1d5Metric
    rw [hf1, hf5, Real.div_rpow h1.le ha.le, Real.div_rpow h5.le ha.le,
      Real.div_rpow h1.le ha.le, Real.div_rpow h5.le ha.le, Real.rpow_neg ha.le,
      ← Real.sqrt_eq_rpow a]
    generalize (a + g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) = A1
    generalize (a + g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) = A5
    generalize (a + g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) = B1
    generalize (a + g * Q5 / U ^ 2) ^ (1/2:ℝ) = B5
    have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    generalize Real.sqrt a = s at hsa hs ⊢
    subst hsa
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev
