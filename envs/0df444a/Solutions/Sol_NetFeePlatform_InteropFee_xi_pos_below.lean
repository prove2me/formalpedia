-- Prove2me | solution 1 for NetFeePlatform.InteropFee.xi_pos_below
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:18:42.415243+00:00
-- url     : https://prove2.me/submissions/bd43fa74-6c41-4015-a305-d03265aaef53

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric
set_option autoImplicit false
open NetFeePlatform.InteropFee

theorem solution {J : ℕ} (hJ : 2 ≤ J) (w c γ lam : ℝ) (hw : 0 ≤ w) (hγ : 0 ≤ γ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∀ τ : ℝ, τ < c - 2 * γ - γ * lam * ((J : ℝ) - 1) → 0 < xi w c γ lam J τ := by
  intro τ hτ
  have hJ2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 0 < Real.exp (-τ) := Real.exp_pos _
  have hD : 0 < w + (J : ℝ) * Real.exp (-τ) := by positivity
  have hn0 : 0 < nSym w J τ := by unfold nSym; positivity
  have hn1 : nSym w J τ < 1 := by
    unfold nSym
    rw [div_lt_one hD]
    nlinarith
  have h1n : 0 < 1 - nSym w J τ := by linarith
  have hphi : 0 ≤ phiSym w J τ := by
    unfold phiSym
    apply div_nonneg _ h1n.le
    apply mul_nonneg (by linarith) hn0.le
  set n := nSym w J τ with hn
  set φ := phiSym w J τ with hφ
  have hA : 0 ≤ γ * lam * ((J : ℝ) - 1) := by
    apply mul_nonneg (mul_nonneg hγ hlam0) (by linarith)
  have h1 : 0 ≤ γ * lam * φ * n := mul_nonneg (mul_nonneg (mul_nonneg hγ hlam0) hphi) hn0.le
  have h2 : 0 ≤ (2 * γ + γ * lam * ((J : ℝ) - 1)) * (1 - n) :=
    mul_nonneg (by linarith) h1n.le
  have h3 : 0 < 1 / (1 - n) := by positivity
  unfold xi
  nlinarith
