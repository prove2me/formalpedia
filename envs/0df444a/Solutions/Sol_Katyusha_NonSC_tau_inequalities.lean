-- Prove2me | solution 1 for Katyusha.NonSC.tau_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:03:01.361987+00:00
-- url     : https://prove2.me/submissions/e0fa5f99-2429-41f5-a3e5-cabc75c6e075

import Mathlib
import Definitions.Def_Katyusha_NonSC_step

open Katyusha.NonSC in
theorem solution (s : ℕ) :
    tau1 s ≤ 1 / 2 ∧
      1 / tau1 s ^ 2 ≥ (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ∧
      (tau1 s + tau2) / tau1 s ^ 2 ≥ tau2 / tau1 (s + 1) ^ 2 := by
  have hx : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h4 : (0 : ℝ) < (s : ℝ) + 4 := by linarith
  have h5 : (0 : ℝ) < (s : ℝ) + 5 := by linarith
  have e0 : tau1 s = 2 / ((s : ℝ) + 4) := rfl
  have e1 : tau1 (s + 1) = 2 / ((s : ℝ) + 5) := by
    unfold tau1; push_cast; ring_nf
  have et : tau2 = 1 / 2 := rfl
  have a1 : 1 / tau1 s ^ 2 = ((s : ℝ) + 4) ^ 2 / 4 := by
    rw [e0]; field_simp; norm_num
  have a2 : (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 = ((s : ℝ) + 3) * ((s : ℝ) + 5) / 4 := by
    rw [e1]; field_simp; ring
  have a3 : (tau1 s + tau2) / tau1 s ^ 2 = (((s : ℝ) + 4) / 2 + ((s : ℝ) + 4) ^ 2 / 8) := by
    rw [e0, et]; field_simp; ring
  have a4 : tau2 / tau1 (s + 1) ^ 2 = ((s : ℝ) + 5) ^ 2 / 8 := by
    rw [e1, et]; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, div_le_iff₀ h4]; linarith
  · rw [a1, a2, ge_iff_le]; nlinarith
  · rw [a3, a4, ge_iff_le]; nlinarith
