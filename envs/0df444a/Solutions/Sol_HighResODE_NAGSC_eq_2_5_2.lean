-- Prove2me | solution 2 for HighResODE.NAGSC.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:54:03.441731+00:00
-- url     : https://prove2.me/submissions/bf5b0c3c-09bc-45e8-8951-3817d773e233

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
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hrr : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hσ0 : 0 ≤ Real.sqrt (μ * s) := Real.sqrt_nonneg _
  have hσ1 : Real.sqrt (μ * s) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hμs
  set σ := Real.sqrt (μ * s) with hσ
  set r := Real.sqrt s with hrdef
  have h1σ : (1 - σ) ≠ 0 := by linarith
  have h1p : (1 + σ) ≠ 0 := by linarith
  have hrne : r ≠ 0 := hr.ne'
  have hs' : s = r * r := hrr.symm
  refine ⟨fun k => ⟨?_, ?_⟩, ?_⟩
  · unfold vel
    rw [smul_smul, ← hrdef]
    rw [show r * (1 / r) = 1 by field_simp, one_smul]
  · -- recursion
    have hx2 : x (k + 1 + 1) = x (k + 1) - s • gradient f (x (k + 1)) +
        ((1 - σ) / (1 + σ)) • ((x (k + 1) - s • gradient f (x (k + 1))) -
          (x k - s • gradient f (x k))) := by
      rw [hx (k + 1), hy (k + 1), hy k]
    unfold vel
    rw [← hrdef, hx2]
    rw [hs']
    match_scalars <;> field_simp <;> ring
  · unfold vel
    have hx1 : x (0 + 1) = x 0 - s • gradient f (x 0) +
        ((1 - σ) / (1 + σ)) • ((x 0 - s • gradient f (x 0)) - x 0) := by
      rw [hx 0, hy 0, hinit]
    rw [← hrdef, hx1, hs']
    match_scalars <;> field_simp <;> ring

