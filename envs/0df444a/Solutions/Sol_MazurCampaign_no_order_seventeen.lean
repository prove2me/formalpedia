-- Prove2me | solution 1 for MazurCampaign.no_order_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:13:15.19898+00:00
-- url     : https://prove2.me/submissions/006949b7-fa19-4540-8033-1bcf78644627

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurHuang_exists_tate_normal_form_of_addOrderOf_gt_three
import Theorems.Thm_MazurHuang_tate_origin_addOrderOf_ne_seventeen

open scoped WeierstrassCurve.Affine

/-- A rational point of order 17 is moved to the marked point of a Tate normal form,
which cannot have order 17. -/
theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 17 := by
  intro x hx
  have hP : addOrderOf (x : (E⁄ℚ).Point) = 17 := by
    rw [← hx]; exact AddSubgroup.addOrderOf_coe x
  obtain ⟨b, c, hb, hEll, h, hord⟩ :=
    MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three E x 17 (by norm_num) hP
  exact MazurHuang.tate_origin_addOrderOf_ne_seventeen b c hb h hord
