-- Prove2me | solution 1 for HessianDamping.DINSC.quad_form_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:23:38.593983+00:00
-- url     : https://prove2.me/submissions/1ac2d909-f004-49ee-b57a-dadcd75c6505

import Mathlib
set_option autoImplicit false

theorem solution (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ)) :
    ∀ X Y : ℝ, 0 ≤ μ / 4 * X ^ 2 + β / (2 * Real.sqrt μ) * Y ^ 2 - β * Real.sqrt μ * X * Y := by
  intro X Y
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hμ' : μ = Real.sqrt μ ^ 2 := (Real.sq_sqrt hμ.le).symm
  set m := Real.sqrt μ with hmdef
  have h1 : 0 ≤ 1 / (2 * m) - β := sub_nonneg.2 hβ
  have h2 : 0 ≤ β * (1 / (2 * m) - β) * Y ^ 2 := by positivity
  have e : μ / 4 * X ^ 2 + β / (2 * m) * Y ^ 2 - β * m * X * Y
      = (m / 2 * X - β * Y) ^ 2 + β * (1 / (2 * m) - β) * Y ^ 2 := by
    rw [hμ']
    field_simp
    ring
  rw [e]
  positivity
