-- Prove2me | solution 1 for MazurCampaign.nine_composite_exclusions
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T09:27:56.650984+00:00
-- url     : https://prove2.me/submissions/9b900bd7-b3ae-48ec-9c0e-e032a7823f96

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_no_order_fourteen
import Theorems.Thm_MazurCampaign_no_order_fifteen
import Theorems.Thm_MazurCampaign_no_order_sixteen
import Theorems.Thm_MazurCampaign_no_order_eighteen
import Theorems.Thm_MazurCampaign_no_order_twenty
import Theorems.Thm_MazurCampaign_no_order_twenty_one
import Theorems.Thm_MazurCampaign_no_order_twenty_four
import Theorems.Thm_MazurCampaign_no_order_twenty_seven
import Theorems.Thm_MazurCampaign_no_order_forty_nine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ n ∈ ({14, 15, 16, 18, 20, 21, 24, 27, 49} : Finset ℕ),
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ n := by
  intro n hn x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MazurCampaign.no_order_fourteen E x
  · exact MazurCampaign.no_order_fifteen E x
  · exact MazurCampaign.no_order_sixteen E x
  · exact MazurCampaign.no_order_eighteen E x
  · exact MazurCampaign.no_order_twenty E x
  · exact MazurCampaign.no_order_twenty_one E x
  · exact MazurCampaign.no_order_twenty_four E x
  · exact MazurCampaign.no_order_twenty_seven E x
  · exact MazurCampaign.no_order_forty_nine E x

#print axioms solution
