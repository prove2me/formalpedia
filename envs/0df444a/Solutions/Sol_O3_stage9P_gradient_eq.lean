-- Prove2me | solution 1 for O3.stage9P_gradient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:32.968606+00:00
-- url     : https://prove2.me/submissions/6fe1d918-9c09-4700-96d5-ae04c804bc18

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_stage9P_zero
import Theorems.Thm_O3_stage9P_succ
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


attribute [local simp] O3.stage9P_zero
attribute [local simp] O3.stage9P_succ

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} {theta : ℕ → ℝ} {g : ℕ → Vec d}
    {k : ℕ} (hθ : theta k ≠ 0) :
    g k = theta k • stage9P theta g (k + 1) -
      (theta k - 1) • stage9P theta g k := by
  funext i
  simp only [stage9P_succ, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  field_simp [hθ]
  ring
end O3
