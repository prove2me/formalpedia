-- Prove2me | solution 1 for HighResODE.NAGSC.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:33:29.985433+00:00
-- url     : https://prove2.me/submissions/8601beda-9d75-42c8-b2d4-e43c8dc916d8

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

set_option autoImplicit false
open HighResODE.NAGSC
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : E n → ℝ) (μ s : ℝ) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ s x y) (hs : 0 < s) (hμs : μ * s < 1) :
    (∀ k : ℕ, x (k + 1) - x k = Real.sqrt s • vel s x k ∧
      vel s x (k + 1) - vel s x k =
        -(2 * Real.sqrt (μ * s) / (1 - Real.sqrt (μ * s))) • vel s x (k + 1)
          - Real.sqrt s • (gradient f (x (k + 1)) - gradient f (x k))
          - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
              (Real.sqrt s • gradient f (x (k + 1)))) ∧
    vel s x 0 = -(2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) • gradient f (x 0) := by
  obtain ⟨hinit, hy, hx⟩ := hrun
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ s = b ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have hsq : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
  set q : ℝ := Real.sqrt (μ * b ^ 2) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hq, Real.sqrt_lt' one_pos]
    simpa using hμs
  have h1q : 1 - q ≠ 0 := by intro h; linarith
  have h1p : 1 + q ≠ 0 := by intro h; linarith
  have hrec : ∀ k : ℕ, x (k + 1 + 1) = x (k + 1) - b ^ 2 • gradient f (x (k + 1))
      + ((1 - q) / (1 + q)) • (x (k + 1) - x k - b ^ 2 • gradient f (x (k + 1))
        + b ^ 2 • gradient f (x k)) := by
    intro k
    have h := hx (k + 1)
    rw [hy (k + 1), hy k] at h
    rw [h]
    module
  refine ⟨?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · simp only [vel, hsq, smul_smul]
      rw [mul_one_div_cancel hb.ne', one_smul]
    · simp only [vel, hsq]
      rw [hrec k]
      match_scalars <;> field_simp <;> ring
  · have h0 : x 1 = x 0 - b ^ 2 • gradient f (x 0)
        + ((1 - q) / (1 + q)) • (-(b ^ 2 • gradient f (x 0))) := by
      have h := hx 0
      rw [hy 0, hinit] at h
      rw [h]
      module
    simp only [vel, hsq, h0]
    match_scalars <;> field_simp <;> ring
