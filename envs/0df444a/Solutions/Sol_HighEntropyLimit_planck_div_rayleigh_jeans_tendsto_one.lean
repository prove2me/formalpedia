-- Prove2me | solution 1 for HighEntropyLimit.planck_div_rayleigh_jeans_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:39:27.856974+00:00
-- url     : https://prove2.me/submissions/d6ef1b0e-28b7-4405-8c42-4253f84a3762

import Mathlib
import Definitions.Def_HighEntropyLimit_blackbody

open Filter Topology HighEntropyLimit

lemma x_div_exp_sub_one :
    Tendsto (fun x : ℝ => x / (Real.exp x - 1)) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at h
  have h2 : Tendsto (fun t : ℝ => t⁻¹ * (Real.exp t - 1)) (𝓝[>] 0) (𝓝 1) :=
    h.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have h3 := h2.inv₀ one_ne_zero
  simp only [inv_one] at h3
  refine h3.congr' ?_
  filter_upwards with t
  rw [mul_inv, inv_inv, div_eq_mul_inv]

theorem solution (h c ν : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hν : 0 < ν) :
    Tendsto (fun β : ℝ => planckSpectrum h c ν β / rayleighJeansSpectrum c ν β) (𝓝[>] 0)
      (𝓝 1) := by
  have hk : 0 < h * ν := mul_pos hh hν
  have h1 : Tendsto (fun β : ℝ => h * ν * β) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun β : ℝ => h * ν * β) (𝓝 0) (𝓝 (h * ν * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact mul_pos hk hβ
  refine (x_div_exp_sub_one.comp h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : (0:ℝ) < β := hβ
  simp only [Function.comp, planckSpectrum, rayleighJeansSpectrum]
  have he : Real.exp (h * β * ν) - 1 ≠ 0 := by
    have : 1 < Real.exp (h * β * ν) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  rw [show h * ν * β = h * β * ν by ring]
  field_simp
