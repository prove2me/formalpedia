-- Prove2me | solution 1 for O3.Stage2Closure.dualityMap_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:36.543781+00:00
-- url     : https://prove2.me/submissions/6ecef878-23cc-465c-a5f9-bff12b8b42c3

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2RouteB_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
attribute [local simp] O3.Stage2RouteD.dualityMap_zero



set_option autoImplicit true
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution {d : ℕ} (u : Point d) : dualityMap 2 u = u := by
  by_cases hu : u = 0
  · subst u
    exact Stage2RouteB.dualityMap_zero (by norm_num)
  · have hn : lpNorm 2 u ≠ 0 := (lpNorm_pos_of_ne_zero hu).ne'
    rw [dualityMap, if_neg hn]
    funext i
    norm_num [powerDualityMap]
end O3.Stage2Closure
