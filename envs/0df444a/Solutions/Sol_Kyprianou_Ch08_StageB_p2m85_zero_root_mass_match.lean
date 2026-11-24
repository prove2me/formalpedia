-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_root_mass_match
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:59:54.753422+00:00
-- url     : https://prove2.me/submissions/b7bbdee8-c65d-46f4-964d-1b735032697d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_laplace_mass_limit
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ) (ψ : ℝ → ℝ) (c : ℝ)
    (hs : ν (Iio (0 : ℝ)) = 0)
    (hp : ∀ s : ℝ, 0 < s → 0 < ψ s)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) = ENNReal.ofReal (s/ψ s))
    (hlim : Tendsto (fun n : ℕ => ψ (1 / ((n : ℝ)+1)) / (1 / ((n : ℝ)+1)))
      atTop (𝓝 c)) :
    (ν univ)⁻¹ = ENNReal.ofReal c := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)
  have hpos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hmass := Kyprianou.Ch08.StageB.p2m89_laplace_mass_limit ν hs
  have hmass' : Tendsto (fun n => ENNReal.ofReal (s n / ψ (s n))) atTop (𝓝 (ν univ)) :=
    hmass.congr' (Eventually.of_forall fun n => hlap (s n) (hpos n))
  have hi := hmass'.inv
  have he : Tendsto (fun n => ENNReal.ofReal (ψ (s n) / s n))
      atTop (𝓝 ((ν univ)⁻¹)) := by
    apply hi.congr'
    apply Eventually.of_forall
    intro n
    change (ENNReal.ofReal (s n / ψ (s n)))⁻¹ = ENNReal.ofReal (ψ (s n) / s n)
    rw [← ENNReal.ofReal_inv_of_pos (div_pos (hpos n) (hp _ (hpos n))), inv_div]
  exact tendsto_nhds_unique he (ENNReal.tendsto_ofReal hlim)
