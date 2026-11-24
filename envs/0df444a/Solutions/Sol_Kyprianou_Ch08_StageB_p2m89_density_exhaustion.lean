-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_density_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:27:50.42127+00:00
-- url     : https://prove2.me/submissions/ad6e7221-f09f-483c-8426-580e5a3de875

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_measurable_mono
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_density_pointwise_limit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))) :
    Tendsto (fun n : ℕ => (∫⁻ y in A, if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0)) atTop
      (𝓝 ((volume.withDensity (fun y : ℝ => ENNReal.ofReal
        (unrestrictedPotentialDensity ψ q (W q) (y - x)))) A)) := by
  classical
  let f (n : ℕ) (y : ℝ) : ℝ≥0∞ := if 0 ≤ y + (n : ℝ) - x then
    ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
      (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y)) else 0
  let g (y : ℝ) := ENNReal.ofReal (unrestrictedPotentialDensity ψ q (W q) (y-x))
  obtain ⟨hf, hm'⟩ := p2m89_density_measurable_mono ψ W q x A hA hW hm hl
  have hlim := p2m89_density_pointwise_limit ψ W q x A hA hW hm hl
  have hi (y : ℝ) : (⨆ n, f n y) = g y :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun n m h => hm' h y)) (hlim y)
  change Tendsto (fun n : ℕ => ∫⁻ y in A, f n y) atTop (𝓝 ((volume.withDensity g) A))
  rw [withDensity_apply g hA]
  have heq : (⨆ n, ∫⁻ y in A, f n y) = ∫⁻ y in A, g y := by
    rw [← lintegral_iSup hf hm']
    exact lintegral_congr hi
  rw [← heq]
  exact tendsto_atTop_iSup (fun n m h => lintegral_mono (hm' h))
