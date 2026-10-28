-- Prove2me | solution 1 for IncInfoDebt.FallenAngel.killedKernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:07:11.224296+00:00
-- url     : https://prove2.me/submissions/bde62b05-3abd-470f-b460-5cfb98975770

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

open IncInfoDebt.FallenAngel in
theorem solution (σ m L a : ℝ) (hP : Standing σ L) :
    killedKernel σ m L a 0 = 0 := by
  obtain ⟨hσ, hL⟩ := hP
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hL' : L ≠ 0 := hL.ne'
  have key : -(1 / (2 * σ ^ 2 * L)) * (0 - a - m * L) ^ 2
      = -(2 * a * m / σ ^ 2) + -(1 / (2 * σ ^ 2 * L)) * (0 - -a - m * L) ^ 2 := by
    field_simp
    ring
  unfold killedKernel freeDensity
  rw [mul_left_comm, ← Real.exp_add, ← key, sub_self]
