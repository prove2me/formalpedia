-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_scalarJ_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:31.109371+00:00
-- url     : https://prove2.me/submissions/e82a76ab-ffe3-4051-b9bf-b65ca359b6f6

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_of_ne_zero
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_zero
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q u : ℝ} (hq : 2 < q) :
    HasDerivAt (O3.Experimental.scalarJ q)
      ((q - 1) * |u| ^ (q - 2)) u := by
  by_cases hu : u = 0
  · subst u
    simpa [Real.zero_rpow (by linarith : q - 2 ≠ 0)] using
      hasDerivAt_scalarJ_zero hq
  · exact hasDerivAt_scalarJ_of_ne_zero hu
end O3.Stage2RouteA
