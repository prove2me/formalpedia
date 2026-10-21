-- Prove2me | solution 1 for HighResODE.NAGC.eq_4_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:56:47.402552+00:00
-- url     : https://prove2.me/submissions/615a831d-7130-4889-a3f6-ab93a1bf2960

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

set_option autoImplicit false

open HighResODE.NAGC
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (s : ℝ) (hs : 0 < s) (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    (∀ k : ℕ, ((k : ℝ) + 4) • (HighResODE.NAGSC.vel s x (k + 1) + Real.sqrt s • gradient f (x (k + 1)))
        - ((k : ℝ) + 1) • (HighResODE.NAGSC.vel s x k + Real.sqrt s • gradient f (x k))
        = -(((k : ℝ) + 1) * Real.sqrt s) • gradient f (x (k + 1))) ∧
    HighResODE.NAGSC.vel s x 0 + Real.sqrt s • gradient f (x 0) = 0 := by
  obtain ⟨hinit, hy, hx⟩ := hrun
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ s = b ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have hsq : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
  have hrec : ∀ k : ℕ, x (k + 1 + 1) = x (k + 1) - b ^ 2 • gradient f (x (k + 1))
      + (((k : ℝ) + 1) / ((k : ℝ) + 4)) • (x (k + 1) - x k - b ^ 2 • gradient f (x (k + 1))
        + b ^ 2 • gradient f (x k)) := by
    intro k
    have h := hx (k + 1)
    rw [hy (k + 1), hy k] at h
    rw [h]
    push_cast
    have : ((k : ℝ) + 1 + 3) = (k : ℝ) + 4 := by ring
    rw [this]
    module
  refine ⟨?_, ?_⟩
  · intro k
    simp only [HighResODE.NAGSC.vel, hsq]
    rw [hrec k]
    have hk4 : (k : ℝ) + 4 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
  · have h0 : x 1 = x 0 - b ^ 2 • gradient f (x 0) := by
      have h := hx 0
      rw [hy 0, hinit] at h
      simp at h
      exact h
    simp only [HighResODE.NAGSC.vel, hsq, h0]
    match_scalars <;> field_simp <;> ring
