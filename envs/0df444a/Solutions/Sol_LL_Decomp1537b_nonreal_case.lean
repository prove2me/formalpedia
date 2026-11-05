-- Prove2me | solution 1 for LL_Decomp1537b.nonreal_case
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:22.01041+00:00
-- url     : https://prove2.me/submissions/4861c20f-7000-4348-a401-19644a005924

import Mathlib

open Finset Real

theorem solution {H : ℝ} (hH : 0 < H) :
    ∃ Y : ℝ, ∀ lN : ℝ, Y ≤ lN → ∀ x ℓ : ℝ, Real.log 2 ≤ x → 1 ≤ ℓ → ℓ ≤ 2 * lN →
      1 / (4 * 10 ^ 4 * (x + (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4))) ≤ H / lN →
      lN / (8 * 10 ^ 4 * H) ≤ x := by
  set c : ℝ := 1 / (8 * 10 ^ 4 * H) with hc
  have hcpos : 0 < c := by positivity
  have h1 : ∀ᶠ t : ℝ in Filter.atTop, Real.log (2 * t) ^ 3 ≤ c ^ 4 / 16 * (2 * t) := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 3)).def (show 0 < c ^ 4 / 16 by positivity)
    have h' := (Filter.tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by norm_num)).eventually h
    filter_upwards [h', Filter.eventually_gt_atTop 0] with t ht ht0
    simp only [id, Real.norm_eq_abs] at ht
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * t)] at ht
    exact (le_abs_self _).trans ht
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.mp h1
  refine ⟨max Y0 2, ?_⟩
  intro lN hlN x ℓ hx hℓ1 hℓ hhyp
  have hl2 : 2 ≤ lN := (le_max_right _ _).trans hlN
  have hlpos : 0 < lN := by linarith
  have hLog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hxpos : 0 < x := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have hApos : 0 ≤ (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (mul_nonneg hℓpos.le hlogℓ) _
  have hlog2l : 0 ≤ Real.log (2 * lN) := Real.log_nonneg (by linarith)
  have hB : (2 * lN * Real.log (2 * lN)) ^ ((3 : ℝ) / 4) ≤ c * lN := by
    have ht := hY0 lN ((le_max_left _ _).trans hlN)
    have hn : 0 ≤ 2 * lN * Real.log (2 * lN) := by positivity
    have h4 : ((2 * lN * Real.log (2 * lN)) ^ ((3 : ℝ) / 4)) ^ 4 = (2 * lN * Real.log (2 * lN)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
      norm_num
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hn _) (by positivity) (by norm_num : (4:ℕ) ≠ 0), h4]
    calc (2 * lN * Real.log (2 * lN)) ^ 3 = 8 * lN ^ 3 * Real.log (2 * lN) ^ 3 := by ring
      _ ≤ 8 * lN ^ 3 * (c ^ 4 / 16 * (2 * lN)) := by gcongr
      _ = (c * lN) ^ 4 := by ring
  have hAB : (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4) ≤ c * lN := by
    refine le_trans (Real.rpow_le_rpow (mul_nonneg hℓpos.le hlogℓ) ?_ (by norm_num)) hB
    have : Real.log ℓ ≤ Real.log (2 * lN) := Real.log_le_log hℓpos hℓ
    exact mul_le_mul hℓ this hlogℓ (by linarith)
  rw [div_le_div_iff₀ (by positivity) hlpos] at hhyp
  rw [div_le_iff₀ (by positivity)]
  have e : 4 * 10 ^ 4 * H * (c * lN) = lN / 2 := by
    rw [hc]; field_simp; norm_num
  have hm : 4 * 10 ^ 4 * H * (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4) ≤ 4 * 10 ^ 4 * H * (c * lN) :=
    mul_le_mul_of_nonneg_left hAB (by positivity)
  nlinarith
