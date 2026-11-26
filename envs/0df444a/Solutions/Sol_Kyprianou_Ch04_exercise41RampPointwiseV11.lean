-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampPointwiseV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:32.258255+00:00
-- url     : https://prove2.me/submissions/03b99a0e-4b21-4a37-94e7-32727ec64714

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41RampValueBoundsV10
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    let r := fun (n : ℕ) (u : ℝ) => min 1 (max 0 (u / ε n))
    let p := fun (n : ℕ) (x : ℝ) => ∫ u in (0 : ℝ)..x, r n u
    Tendsto (fun n => p n x) atTop (𝓝 (max 0 x)) := by
  let r := fun (n : ℕ) (u : ℝ) => min 1 (max 0 (u / ε n))
  let p := fun (n : ℕ) (x : ℝ) => ∫ u in (0 : ℝ)..x, r n u
  change Tendsto (fun n => p n x) atTop (𝓝 (max 0 x))
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
  obtain ⟨_,_,hupper,hlower⟩ := exercise41RampValueBoundsV10 (ε n) (hε n) x
  change p n x ≤ max 0 x at hupper
  change max 0 x - ε n ≤ p n x at hlower
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith
