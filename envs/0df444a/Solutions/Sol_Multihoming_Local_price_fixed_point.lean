-- Prove2me | solution 1 for Multihoming.Local.price_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:50:03.422552+00:00
-- url     : https://prove2.me/submissions/c14b2fe5-60c0-45f0-a078-0fd6043c8e2b

import Mathlib
import Definitions.Def_Multihoming_Local_Model
open Multihoming.Local

theorem solution(t μ ei ej : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    priceM t μ ei ej = reactM t μ ei ej (priceM t μ ej ei) ∧
      priceM t μ ej ei = reactM t μ ej ei (priceM t μ ei ej) := by
  have h2 : 2 * t - μ ≠ 0 := by linarith
  have h3 : 2 * t + μ ≠ 0 := by linarith
  have h2' : t * 2 - μ ≠ 0 := by linarith
  have h3' : t * 2 + μ ≠ 0 := by linarith
  have h1 : t ≠ 0 := ht.ne'
  unfold priceM reactM
  rw [show 4 * t ^ 2 - μ ^ 2 = (2 * t - μ) * (2 * t + μ) by ring]
  constructor <;> field_simp <;> ring
