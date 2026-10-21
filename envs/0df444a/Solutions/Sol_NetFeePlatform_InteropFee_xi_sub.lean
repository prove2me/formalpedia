-- Prove2me | solution 1 for NetFeePlatform.InteropFee.xi_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:17:59.263407+00:00
-- url     : https://prove2.me/submissions/9dbcc453-7dfb-4664-b40d-684a15dd258e

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric
set_option autoImplicit false
open NetFeePlatform.InteropFee

theorem solution {J : ℕ} (hJ : 2 ≤ J) (w c γ lamLo lamHi τ : ℝ) (hw : 0 ≤ w) :
    xi w c γ lamHi J τ
        = xi w c γ lamLo J τ - γ * (lamHi - lamLo) * ((J : ℝ) - 1 - phiSym w J τ) * nSym w J τ ∧
      ((3 ≤ J ∨ 0 < w) → 0 < (J : ℝ) - 1 - phiSym w J τ) ∧
      (J = 2 → w = 0 → (J : ℝ) - 1 - phiSym w J τ = 0) := by
  have hJ2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 0 < Real.exp (-τ) := Real.exp_pos _
  have hD : 0 < w + (J : ℝ) * Real.exp (-τ) := by positivity
  have hE : 0 < w + ((J : ℝ) - 1) * Real.exp (-τ) := by
    have : (0 : ℝ) < ((J : ℝ) - 1) * Real.exp (-τ) := by
      apply mul_pos (by linarith) he
    linarith
  have key : (J : ℝ) - 1 - phiSym w J τ =
      ((J : ℝ) - 1) * (w + ((J : ℝ) - 2) * Real.exp (-τ)) / (w + ((J : ℝ) - 1) * Real.exp (-τ)) := by
    unfold phiSym nSym
    have h1 : 1 - Real.exp (-τ) / (w + (J : ℝ) * Real.exp (-τ)) =
        (w + ((J : ℝ) - 1) * Real.exp (-τ)) / (w + (J : ℝ) * Real.exp (-τ)) := by
      field_simp; ring
    rw [h1]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold xi; ring
  · intro h
    rw [key]
    apply div_pos _ hE
    apply mul_pos (by linarith)
    rcases h with h | h
    · have : (3 : ℝ) ≤ J := by exact_mod_cast h
      have : 0 < ((J : ℝ) - 2) * Real.exp (-τ) := mul_pos (by linarith) he
      linarith
    · have : 0 ≤ ((J : ℝ) - 2) * Real.exp (-τ) := mul_nonneg (by linarith) he.le
      linarith
  · intro h2 hw0
    rw [key]
    subst h2; subst hw0
    simp
