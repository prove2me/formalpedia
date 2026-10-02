-- Prove2me | solution 1 for MilnorDynamics.exp_cayley_image_subset_exterior
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-02T10:09:33.460198+00:00
-- url     : https://prove2.me/submissions/f116da96-0e2f-4b9c-92ca-6b3b519e3883

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

open MilnorDynamics

/-- `exp_cayley_image_subset_exterior` is false as published.

The statement asserts `∀ z : ℂ, 1 < ‖exp ((z + 1) / (1 - z))‖` with **no** domain
hypothesis.  Take `z = -1`.  Then `z + 1 = 0`, so the argument is `0 / 2 = 0` and
`exp 0 = 1`, giving `‖1‖ = 1`, which is not `> 1`.

The disc hypothesis is exactly what the statement drops.  Its own natural-language
text derives the bound from the **Proved** lemma `cayley_disk_lt_halfplane`
(`0 < ((z + 1) / (1 - z)).re`), but that lemma carries `hz : z ∈ Metric.ball 0 1`,
and the conclusion here has dropped it.  With the hypothesis restored the statement
is true and is already **Proved** as `exp_cayley_image_exterior_on_disc`
(4ed70a1d-f537-4a3c-8dda-0c557f16d87c).

Arithmetic only: `Complex.exp_zero` and `norm_one`. -/
theorem solution :
    ¬ (∀ z : ℂ, 1 < ‖Complex.exp ((z + 1) / (1 - z))‖) := by
  intro hall
  have hone := hall (-1 : ℂ)
  have harg : ((-1 + 1) / (1 - (-1)) : ℂ) = 0 := by
    norm_num
  rw [harg, Complex.exp_zero, norm_one] at hone
  norm_num at hone

