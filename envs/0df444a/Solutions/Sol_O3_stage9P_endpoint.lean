-- Prove2me | solution 1 for O3.stage9P_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:02.061884+00:00
-- url     : https://prove2.me/submissions/4b1f9bd9-c6ad-4edf-9c29-0f6a134cb03a

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
    {n : ℕ} (hθn : theta n = 1) :
    stage9P theta g (n + 1) = g n := by
  rw [stage9P_succ, hθn]
  simp
end O3
