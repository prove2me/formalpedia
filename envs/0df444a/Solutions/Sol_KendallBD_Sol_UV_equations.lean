-- Prove2me | solution 1 for KendallBD.Sol.UV_equations
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:17:03.230559+00:00
-- url     : https://prove2.me/submissions/afe212df-e64a-49f2-972e-7508981e0b81

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

theorem solution (lam mu ξ η : ℝ → ℝ) (t ξ' η' : ℝ)
    (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t)
    (hU : 1 - ξ t ≠ 0)
    (hpair : (η t * ξ' - ξ t * η') + η' = lam t * (1 - ξ t) * (1 - η t) ∧
      ξ' = mu t * (1 - ξ t) * (1 - η t)) :
    -ξ' = -mu t * (1 - η t) * (1 - ξ t) ∧
      -η' = (mu t - lam t) * (1 - η t) - mu t * (1 - η t) ^ 2 := by
  constructor
  · rw [hpair.2]
    ring
  · have h : (1 - ξ t) *
        (-η' - ((mu t - lam t) * (1 - η t) - mu t * (1 - η t) ^ 2)) = 0 := by
      linear_combination -hpair.1 + η t * hpair.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hU)
