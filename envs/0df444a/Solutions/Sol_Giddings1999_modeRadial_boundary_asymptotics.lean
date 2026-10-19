-- Prove2me | solution 1 for Giddings1999.modeRadial_boundary_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:40:50.574991+00:00
-- url     : https://prove2.me/submissions/65e67615-902a-44a6-a290-5159019be622

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology
open Giddings1999

theorem solution (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (n l : ℕ) :
    ∃ k : ℝ, k ≠ 0 ∧
      Tendsto (fun r => modeRadial d m R n l r / cos r ^ twoHPlus d m R) (𝓝[<] (π / 2)) (𝓝 k) := by
  set α : ℝ := (l : ℝ) + (d : ℝ) / 2 - 1
  set ν := nu d m R
  have hν : 0 ≤ ν := by simp only [ν, nu]; positivity
  have hP : jacobiP n α ν (-1) = gbinom (n + ν) n * (-1) ^ n := by
    unfold jacobiP
    rw [Finset.sum_eq_single n]
    · simp [gbinom]; left; norm_num
    · intro s hs hsn
      have : n - s ≠ 0 := by
        have := Finset.mem_range.1 hs; omega
      simp [zero_pow this]
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  have hg : 0 < gbinom (n + ν) n := by
    unfold gbinom
    apply div_pos _ (by positivity)
    apply descPochhammer_pos
    linarith
  refine ⟨jacobiP n α ν (-1), ?_, ?_⟩
  · rw [hP]; exact mul_ne_zero hg.ne' (pow_ne_zero _ (by norm_num))
  have hcont : Continuous (fun r : ℝ => sin r ^ l * jacobiP n α ν (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  have hlim := (hcont.tendsto (π / 2)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
  have h2 : 2 * (π / 2) = π := by ring
  simp only [sin_pi_div_two, h2, cos_pi, one_pow, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have hb : 0 < cos r ^ twoHPlus d m R := rpow_pos_of_pos hc _
  simp only [modeRadial, α, ν]
  field_simp
