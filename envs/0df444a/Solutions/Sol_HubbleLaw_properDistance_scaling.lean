-- Prove2me | solution 1 for HubbleLaw.properDistance_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:50:20.66088+00:00
-- url     : https://prove2.me/submissions/c8727e5b-0bb8-49a4-88c1-2f1a4185d959

import Mathlib
import Definitions.Def_HubbleLawDefs

/-! 1ef54657 HubbleLaw.properDistance_scaling: the proper distance is `‖a t • x - a t • y‖ =
|a t| * ‖x - y‖`, so with `a t, a t₀ > 0` the ratio of proper distances at `t` and `t₀` is
`a t / a t₀`. No `Theorems.*` module is imported. -/

set_option autoImplicit false

theorem solution (a : ℝ → ℝ) (t t₀ : ℝ) (ht : 0 < a t) (ht₀ : 0 < a t₀)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    HubbleLaw.properDistance a x y t = a t / a t₀ * HubbleLaw.properDistance a x y t₀ := by
  unfold HubbleLaw.properDistance HubbleLaw.properPosition
  rw [← smul_sub, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg ht₀.le]
  field_simp

