-- Prove2me | solution 1 for NetFeePlatform.Competition.gChar_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:17:09.640011+00:00
-- url     : https://prove2.me/submissions/cbe2214b-243b-4b9d-8fd3-2c712d3194c5

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar
set_option autoImplicit false
open NetFeePlatform.Competition

theorem solution (γ : ℝ) (J : ℕ) (hJ : 2 ≤ J) :
    Filter.Tendsto (gChar γ J) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  have hJ1 : (1 : ℝ) ≤ (J : ℝ) - 1 := by
    have : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hJ0 : (J : ℝ) - 1 ≠ 0 := by linarith
  set h : ℝ → ℝ := fun n => - Real.log ((J : ℝ) - 1) - Real.log (1 - n) + 1 / (1 - n / ((J : ℝ) - 1))
    - 2 * γ * (n / ((J : ℝ) - 1)) + 2 * γ * (1 - n) with hh
  have hcont : ContinuousAt h 0 := by
    have h1 : ContinuousAt (fun n : ℝ => Real.log (1 - n)) 0 := by
      apply ContinuousAt.log (by fun_prop)
      norm_num
    have h2 : ContinuousAt (fun n : ℝ => 1 / (1 - n / ((J : ℝ) - 1))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      simp
    have h3 : ContinuousAt (fun n : ℝ => 2 * γ * (n / ((J : ℝ) - 1))) 0 := by fun_prop
    have h4 : ContinuousAt (fun n : ℝ => 2 * γ * (1 - n)) 0 := by fun_prop
    exact (((continuousAt_const.sub h1).add h2).sub h3).add h4
  have hlim : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds (h 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hf : Filter.Tendsto (fun n : ℝ => Real.log n - 1 / n) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    have b : Filter.Tendsto (fun n : ℝ => - (1 / n)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
      simp only [one_div]
      exact Filter.tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero
    refine Filter.tendsto_atBot_mono' _ ?_ b
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with n hn
    have : Real.log n ≤ 0 := Real.log_nonpos hn.1.le hn.2.le
    linarith
  have := hf.atBot_add hlim
  refine this.congr (fun n => ?_)
  simp only [hh, gChar]
  ring
