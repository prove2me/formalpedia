-- Prove2me | solution 1 for InfoInundation.Screening.part_b_constant_score
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:31:59.729497+00:00
-- url     : https://prove2.me/submissions/3f6254e8-8c07-423e-bdc6-7badbfaa53f0

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoInundation.Screening

theorem solution (σ : ℝ) (hσ : 0 < σ) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    sdScore (Measure.dirac σ) μ s z = s - nextSd s σ ∧
      varScore (Measure.dirac σ) μ s z = s ^ 2 - nextSd s σ ^ 2 := by
  have hL : likelihood μ s σ z ≠ 0 := by
    have hw : 0 < Real.sqrt (2 * (σ ^ 2 + s ^ 2)) := Real.sqrt_pos.2 (by positivity)
    unfold likelihood psi
    have : 0 < 1 / (Real.sqrt Real.pi * Real.sqrt (2 * (σ ^ 2 + s ^ 2))) * 
      Real.exp (-((z - μ) ^ 2 / Real.sqrt (2 * (σ ^ 2 + s ^ 2)) ^ 2)) := by positivity
    exact this.ne'
  have key : ∀ h : ℝ → ℝ, postExp (Measure.dirac σ) μ s z h = h σ := by
    intro h
    unfold postExp
    rw [integral_dirac, integral_dirac]
    field_simp
  constructor
  · unfold sdScore; rw [key]
  · unfold varScore; rw [key]
