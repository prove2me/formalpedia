-- Prove2me | solution 1 for GlynnSTS.Limit.hmap_sigmaB
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:06:43.923988+00:00
-- url     : https://prove2.me/submissions/8df32d31-0860-4d86-aed0-ee879b27d2bc

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

set_option autoImplicit false
open GlynnSTS.Limit

theorem solution {Ω : Type*} (B : Ω → C(unitInterval, ℝ)) (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x) (σ : ℝ) (hσ : 0 < σ) :
    ∀ ω, hmap g (σ • B ω) = B ω 1 / g (B ω) := by
  intro ω
  unfold hmap
  rw [hhom σ hσ]
  by_cases h : g (B ω) = 0
  · simp [h]
  · have h' : σ * g (B ω) ≠ 0 := mul_ne_zero hσ.ne' h
    simp only [h', h, ne_eq, not_false_eq_true, if_true]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
