-- Prove2me | solution 1 for MazurCampaign.no_prime_ge_seventeen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T13:32:46.211818+00:00
-- url     : https://prove2.me/submissions/c7ebd228-642f-4d1f-bdb9-d7ef151ec41e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Reduction of the mission leaf MazurCampaign.no_prime_ge_seventeen to three cases:
p = 17, p = 19 and p ≥ 23 (every prime p ≥ 17 other than 17 and 19 is at least 23).

Author: Xiang Huang
License: Apache-2.0
-/
import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_no_order_seventeen
import Theorems.Thm_MazurCampaign_no_order_nineteen
import Theorems.Thm_MazurCampaign_no_prime_ge_twenty_three

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ p : ℕ, p.Prime → 17 ≤ p →
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ p := by
  intro p hp h17 x
  have hcases : p = 17 ∨ p = 19 ∨ 23 ≤ p := by
    by_contra h
    push_neg at h
    obtain ⟨h1, h2, h3⟩ := h
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rcases hcases with rfl | rfl | h23
  · exact MazurCampaign.no_order_seventeen E x
  · exact MazurCampaign.no_order_nineteen E x
  · exact MazurCampaign.no_prime_ge_twenty_three E p hp h23 x
