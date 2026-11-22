-- Prove2me | solution 1 for NoHair.Weyl.kerr_ernst_axis_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:29:07.017803+00:00
-- url     : https://prove2.me/submissions/54b200b4-7aaa-4ffc-8995-44dc58f1acd7

import Definitions.Def_NoHair_kerrWeylModel

open NoHair.Weyl Filter Topology

private theorem prolate_at_axis (ℓ z : ℝ) :
    Tendsto (fun s : ℝ => prolateRadius ℓ (s,z)) atBot (𝓝 ((|z-ℓ|+|z+ℓ|)/2)) := by
  have he : Tendsto (fun s : ℝ => Real.exp (2*s)) atBot (𝓝 0) := by
    simpa only [two_mul, Real.exp_add, mul_zero] using Real.tendsto_exp_atBot.mul Real.tendsto_exp_atBot
  have side (k : ℝ) : Tendsto (fun s : ℝ => Real.sqrt (Real.exp (2*s)+k^2)) atBot (𝓝 |k|) := by
    rw [← Real.sqrt_sq_eq_abs k]
    simpa only [zero_add] using (he.add_const (k^2)).sqrt
  exact ((side (z-ℓ)).add (side (z+ℓ))).div_const 2

private theorem axial_limits {m a ℓ z L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (he : Real.sqrt (m^2-a^2) = ℓ)
    (hR : Tendsto (fun s : ℝ => prolateRadius ℓ (s,z)) atBot (𝓝 L)) :
    Tendsto (fun s : ℝ => (kerrErnst m a).normSq (s,z)) atBot
      (𝓝 (kerrAxialNorm m a (m+L) (z/L))) ∧
    Tendsto (fun s : ℝ => (kerrErnst m a).twist (s,z)) atBot
      (𝓝 (kerrAxialTwist m a (m+L) (z/L))) := by
  have hr : Tendsto (fun s : ℝ => m + prolateRadius ℓ (s,z)) atBot (𝓝 (m+L)) :=
    tendsto_const_nhds.add hR
  have hc : Tendsto (fun s : ℝ => z / prolateRadius ℓ (s,z)) atBot (𝓝 (z/L)) :=
    tendsto_const_nhds.div hR hL.ne'
  have hden : (m+L)^2 + a^2*(z/L)^2 ≠ 0 := by positivity
  have hX : ContinuousAt (fun q : ℝ × ℝ => kerrAxialNorm m a q.1 q.2) (m+L,z/L) := by
    unfold kerrAxialNorm
    fun_prop (disch := assumption)
  have hY : ContinuousAt (fun q : ℝ × ℝ => kerrAxialTwist m a q.1 q.2) (m+L,z/L) := by
    unfold kerrAxialTwist
    fun_prop (disch := assumption)
  constructor
  · simpa [kerrErnst, he, Function.comp_def] using hX.tendsto.comp (hr.prodMk_nhds hc)
  · simpa [kerrErnst, he, Function.comp_def] using hY.tendsto.comp (hr.prodMk_nhds hc)

theorem solution (m a ℓ : ℝ) (hm : 0 < m) (hℓ : 0 ≤ ℓ)
    (hmatch : m^2 - a^2 = ℓ^2) :
    HasAxisData (kerrErnst m a) ℓ (m*a) := by
  have hroot : Real.sqrt (m^2-a^2) = ℓ := by rw [hmatch, Real.sqrt_sq hℓ]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hz0 : 0 < z := hℓ.trans_lt hz
    have hR := prolate_at_axis ℓ z
    have hval : (|z-ℓ|+|z+ℓ|)/2 = z := by
      rw [abs_of_nonneg (sub_nonneg.mpr hz.le), abs_of_nonneg (by linarith : 0 ≤ z+ℓ)]
      ring
    rw [hval] at hR
    obtain ⟨hX,hY⟩ := axial_limits (a:=a) hm hz0 hroot hR
    have hX0 : kerrAxialNorm m a (m+z) (z/z) = 0 := by simp [kerrAxialNorm, hz0.ne']
    have hY0 : kerrAxialTwist m a (m+z) (z/z) = 4*(m*a) := by
      simp [kerrAxialTwist, hz0.ne'] <;> ring
    exact ⟨hX0 ▸ hX, hY0 ▸ hY⟩
  · intro z hz
    have hz0 : z < 0 := by linarith
    have hR := prolate_at_axis ℓ z
    have hval : (|z-ℓ|+|z+ℓ|)/2 = -z := by
      rw [abs_of_nonpos (by linarith : z-ℓ ≤ 0), abs_of_nonpos (by linarith : z+ℓ ≤ 0)]
      ring
    rw [hval] at hR
    obtain ⟨hX,hY⟩ := axial_limits (a:=a) hm (neg_pos.mpr hz0) hroot hR
    have hcos : z/(-z) = -1 := by simp [hz0.ne]
    have hX0 : kerrAxialNorm m a (m+ -z) (z/(-z)) = 0 := by simp [kerrAxialNorm, hcos]
    have hY0 : kerrAxialTwist m a (m+ -z) (z/(-z)) = -(4*(m*a)) := by
      simp [kerrAxialTwist, hcos] <;> ring
    exact ⟨hX0 ▸ hX, hY0 ▸ hY⟩
  · intro z hz
    have hlp := lt_of_le_of_lt (abs_nonneg z) hz
    obtain ⟨hlo,hhi⟩ := abs_lt.mp hz
    have hR := prolate_at_axis ℓ z
    have hval : (|z-ℓ|+|z+ℓ|)/2 = ℓ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hhi.le), abs_of_nonneg (by linarith : 0 ≤ z+ℓ)]
      ring
    rw [hval] at hR
    have h₁ : -(1 : ℝ) < z/ℓ := (lt_div_iff₀ hlp).2 (by linarith)
    have h₂ : z/ℓ < 1 := (div_lt_iff₀ hlp).2 (by linarith)
    have hsin : 0 < 1-(z/ℓ)^2 := by
      nlinarith [mul_pos (show 0 < 1-z/ℓ by linarith) (show 0 < 1+z/ℓ by linarith)]
    refine ⟨kerrAxialNorm m a (m+ℓ) (z/ℓ), ?_, (axial_limits (a:=a) hm hlp hroot hR).1⟩
    unfold kerrAxialNorm
    positivity
