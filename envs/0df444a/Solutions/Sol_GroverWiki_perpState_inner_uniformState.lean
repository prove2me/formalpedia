-- Prove2me | solution 1 for GroverWiki.perpState_inner_uniformState
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:05:05.72408+00:00
-- url     : https://prove2.me/submissions/15305cf9-998d-430e-a0d5-ac4666778633

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (hN : 2 ≤ N) (ω : Fin N) :
    star (perpState ω) ⬝ᵥ uniformState N = (Real.sqrt (((N : ℝ) - 1) / N) : ℂ) := by
  classical
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have ht : Real.sqrt ((N : ℝ) - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hsq := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)
  have hreal : ((N : ℝ) - 1) * (Real.sqrt ((N : ℝ) - 1))⁻¹ *
      (Real.sqrt N)⁻¹ = Real.sqrt (((N : ℝ) - 1) / N) := by
    rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)]
    field_simp
    nlinarith [hsq]
  let c : ℂ := (Real.sqrt ((N : ℝ) - 1) : ℂ)⁻¹
  let d : ℂ := (Real.sqrt (N : ℝ) : ℂ)⁻¹
  calc
    star (perpState ω) ⬝ᵥ uniformState N =
        ∑ j : Fin N, (c * d - if j = ω then c * d else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : j = ω
      · simp [perpState, uniformState, he, c, d, Complex.ofReal_inv]
      · simp [perpState, uniformState, he, c, d, Complex.ofReal_inv]
    _ = (N : ℂ) * (c * d) - c * d := by simp [Finset.sum_sub_distrib]
    _ = ((N : ℂ) - 1) * c * d := by ring
    _ = (Real.sqrt (((N : ℝ) - 1) / N) : ℂ) := by
      dsimp [c, d]
      exact_mod_cast hreal
