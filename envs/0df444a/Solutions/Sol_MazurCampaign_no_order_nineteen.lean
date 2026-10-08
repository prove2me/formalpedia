-- Prove2me | solution 1 for MazurCampaign.no_order_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:12:36.035617+00:00
-- url     : https://prove2.me/submissions/30def02e-368f-499f-824d-4f2e89e9b243

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurHuang_exists_tate_normal_form_of_addOrderOf_gt_three
import Theorems.Thm_MazurHuang_tate_origin_addOrderOf_ne_nineteen

open scoped WeierstrassCurve.Affine

/-- A rational point of order 19 is moved to the marked point of a Tate normal form,
which cannot have order 19. -/
theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 19 := by
  intro x hx
  have hP : addOrderOf (x : (E⁄ℚ).Point) = 19 := by
    rw [← hx]; exact AddSubgroup.addOrderOf_coe x
  obtain ⟨b, c, hb, hEll, h, hord⟩ :=
    MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three E x 19 (by norm_num) hP
  exact MazurHuang.tate_origin_addOrderOf_ne_nineteen b c hb h hord
