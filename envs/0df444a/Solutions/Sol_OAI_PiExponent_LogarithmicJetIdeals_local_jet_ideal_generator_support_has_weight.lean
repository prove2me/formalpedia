-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_support_has_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T12:53:57.218732+00:00
-- url     : https://prove2.me/submissions/a63f6a02-ba0f-4433-832a-99c099298997

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ k, 0 < w k)
    (hT : ∀ k : Fin m,
      InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (hsupport :
      (∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0) ∨
        (T i ≤ b 0 ∧ ∀ j : Fin m, b j.succ = 0)) :
    InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) := by
  classical
  rcases hsupport with hone | ⟨hTle, hzero⟩
  · simp [InterpolationMatrix.rowWeights, hone]
  · have hcast : (T i : ℝ) ≤ (b 0 : ℝ) := by exact_mod_cast hTle
    have hmul : (T i : ℝ) * v0 ≤ (b 0 : ℝ) * v0 :=
      mul_le_mul_of_nonneg_right hcast (le_of_lt hv0)
    calc
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0 := hT i
      _ ≤ (b 0 : ℝ) * v0 := hmul
      _ = ∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ) := by
        rw [Fin.sum_univ_succ]
        simp [InterpolationMatrix.rowWeights, hzero]
        ring