-- Prove2me | solution 2 for NoHair.Weyl.kerr_ernst_axis_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:33:09.122894+00:00
-- url     : https://prove2.me/submissions/3b7248bf-8986-40b6-9ac1-06c56732b85c

import Mathlib
import Definitions.Def_NoHair_kerrWeylModel

open Filter NoHair.Weyl
open scoped Topology

private theorem radiusLimit (ℓ z : ℝ) :
    Tendsto (fun s : ℝ => prolateRadius ℓ (s, z)) atBot
      (𝓝 ((|z - ℓ| + |z + ℓ|) / 2)) := by
  have he : Tendsto (fun s : ℝ => Real.exp (2 * s)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id)
  have hdist (w : ℝ) : Tendsto (fun s : ℝ => Real.sqrt (Real.exp (2 * s) + w ^ 2))
      atBot (𝓝 |w|) := by
    rw [← Real.sqrt_sq_eq_abs w]
    apply Filter.Tendsto.sqrt
    simpa only [zero_add] using (he.add (tendsto_const_nhds (x := w ^ 2)))
  exact ((hdist (z - ℓ)).add (hdist (z + ℓ))).div_const 2

set_option maxHeartbeats 800000 in
private theorem potentialLimits (m a ℓ z b : ℝ) (hm : 0 < m) (hb : 0 < b)
    (hroot : Real.sqrt (m ^ 2 - a ^ 2) = ℓ)
    (hR : Tendsto (fun s : ℝ => prolateRadius ℓ (s, z)) atBot (𝓝 b)) :
    Tendsto (fun s : ℝ => (kerrErnst m a).normSq (s, z)) atBot
        (𝓝 (kerrAxialNorm m a (m + b) (z / b))) ∧
    Tendsto (fun s : ℝ => (kerrErnst m a).twist (s, z)) atBot
        (𝓝 (kerrAxialTwist m a (m + b) (z / b))) := by
  let r := fun s : ℝ => m + prolateRadius ℓ (s, z)
  let c := fun s : ℝ => z / prolateRadius ℓ (s, z)
  have hr : Tendsto r atBot (𝓝 (m+b)) := (tendsto_const_nhds (x := m)).add hR
  have hc : Tendsto c atBot (𝓝 (z/b)) := (tendsto_const_nhds (x := z)).div hR hb.ne'
  have hconst (k : ℝ) : Tendsto (fun _ : ℝ => k) atBot (𝓝 k) := tendsto_const_nhds
  have hf := (hconst 1).sub (hc.pow 2)
  have hd := (hr.pow 2).add ((hconst (a^2)).mul (hc.pow 2))
  have hden : (m+b)^2 + a^2*(z/b)^2 ≠ 0 := by positivity
  have hx := hf.mul (((hr.pow 2).add (hconst (a^2))).add
    (((((hconst (2*m)).mul hr).mul (hconst (a^2))).mul hf).div hd hden))
  have hy := ((hconst (2*m*a)).mul (((hconst 3).mul hc).sub (hc.pow 3))).add
    ((((hconst (2*m*a^3)).mul hc).mul (hf.pow 2)).div hd hden)
  unfold kerrErnst
  rw [hroot]
  exact ⟨hx, hy⟩

theorem solution (m a ℓ : ℝ) (hm : 0 < m) (hℓ : 0 ≤ ℓ)
    (hmatch : m^2 - a^2 = ℓ^2) :
    HasAxisData (kerrErnst m a) ℓ (m*a) := by
  have hroot : Real.sqrt (m ^ 2 - a ^ 2) = ℓ := by rw [hmatch, Real.sqrt_sq hℓ]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hz0 : 0 < z := lt_of_le_of_lt hℓ hz
    have hr : (|z - ℓ| + |z + ℓ|) / 2 = z := by
      rw [abs_of_pos (by linarith : 0 < z - ℓ), abs_of_pos (by linarith : 0 < z + ℓ)]
      ring
    have h := potentialLimits m a ℓ z z hm hz0 hroot (by simpa only [hr] using radiusLimit ℓ z)
    rw [div_self hz0.ne'] at h
    have ht : kerrAxialTwist m a (m + z) 1 = 4 * (m * a) := by
      norm_num [kerrAxialTwist] <;> ring
    simpa only [ht, kerrAxialNorm, one_pow, sub_self, zero_mul] using h
  · intro z hz
    have hz0 : 0 < -z := by linarith
    have hr : (|z - ℓ| + |z + ℓ|) / 2 = -z := by
      rw [abs_of_neg (by linarith : z - ℓ < 0), abs_of_neg (by linarith : z + ℓ < 0)]
      ring
    have h := potentialLimits m a ℓ z (-z) hm hz0 hroot (by simpa only [hr] using radiusLimit ℓ z)
    have hc : z / -z = -1 := (div_eq_iff hz0.ne').2 (by ring)
    rw [hc] at h
    have hn : kerrAxialNorm m a (m + -z) (-1) = 0 := by norm_num [kerrAxialNorm]
    have ht : kerrAxialTwist m a (m + -z) (-1) = -(4 * (m * a)) := by
      norm_num [kerrAxialTwist] <;> ring
    simpa only [hn, ht] using h
  · intro z hz
    have hpos := lt_of_le_of_lt (abs_nonneg z) hz
    obtain ⟨hzlo, hzhi⟩ := abs_lt.mp hz
    have hr : (|z - ℓ| + |z + ℓ|) / 2 = ℓ := by
      rw [abs_of_neg (by linarith : z - ℓ < 0), abs_of_pos (by linarith : 0 < z + ℓ)]
      ring
    refine ⟨kerrAxialNorm m a (m + ℓ) (z / ℓ), ?_,
      (potentialLimits m a ℓ z ℓ hm hpos hroot (by simpa only [hr] using radiusLimit ℓ z)).1⟩
    have hc : |z / ℓ| < 1 := by
      rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
      exact hz
    have hf : 0 < 1 - (z / ℓ) ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 hc)
    unfold kerrAxialNorm
    exact mul_pos hf (by positivity)
