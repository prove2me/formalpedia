-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanValue_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:25:48.378224+00:00
-- url     : https://prove2.me/submissions/ba152751-80f0-4e6b-8ad8-40cf301d22e6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (K phi : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier := Real.log (K * phi / (1 + phi))
    Continuous (mckeanValue K barrier phi) := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  change Continuous
    (fun y : ℝ =>
      if y < b then K - Real.exp y
      else (K - Real.exp b) * Real.exp (-phi * (y - b)))
  have hc : Continuous (fun y : ℝ =>
      if y ≤ b then K - Real.exp y
      else (K - Real.exp b) * Real.exp (-phi * (y - b))) := by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · exact continuous_id
    · exact continuous_const
    · intro y hy
      subst y
      simp
  have hEq :
      (fun y : ℝ =>
        if y < b then K - Real.exp y
        else (K - Real.exp b) * Real.exp (-phi * (y - b))) =
      (fun y : ℝ =>
        if y ≤ b then K - Real.exp y
        else (K - Real.exp b) * Real.exp (-phi * (y - b))) := by
    funext y
    rcases lt_trichotomy y b with hlt | heq | hgt
    · simp [hlt, hlt.le]
    · subst y
      simp
    · simp [not_lt.mpr hgt.le, not_le.mpr hgt]
  rw [hEq]
  exact hc
