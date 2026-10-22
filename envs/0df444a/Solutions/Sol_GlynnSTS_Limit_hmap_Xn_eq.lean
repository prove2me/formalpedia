-- Prove2me | solution 1 for GlynnSTS.Limit.hmap_Xn_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:06:45.232986+00:00
-- url     : https://prove2.me/submissions/4073978a-b7f5-4bed-bf2e-812047a799b0

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

set_option autoImplicit false
open GlynnSTS.Limit

theorem solution {Ω : Type*} (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ : ℝ)
    (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x)
    (hshift : ∀ β : ℝ, ∀ x, g (x - β • kfun) = g x) :
    ∀ n : ℕ, 1 ≤ n → ∀ ω, hmap g (Xn Ybar μ n ω) = (Ybar n ω 1 - μ) / g (Ybar n ω) := by
  intro n hn ω
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hg : g (Xn Ybar μ n ω) = Real.sqrt n * g (Ybar n ω) := by
    unfold Xn
    rw [hhom _ hs, hshift]
  have hk : (kfun : C(unitInterval, ℝ)) 1 = 1 := rfl
  have hev : (Xn Ybar μ n ω) 1 = Real.sqrt n * (Ybar n ω 1 - μ) := by
    unfold Xn
    simp [hk]
  unfold hmap
  rw [hg, hev]
  by_cases h : g (Ybar n ω) = 0
  · simp [h]
  · have h' : Real.sqrt n * g (Ybar n ω) ≠ 0 := mul_ne_zero hs.ne' h
    simp only [h', h, ne_eq, not_false_eq_true, if_true]
    field_simp
