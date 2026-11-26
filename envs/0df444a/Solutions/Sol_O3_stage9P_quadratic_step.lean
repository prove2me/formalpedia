-- Prove2me | solution 1 for O3.stage9P_quadratic_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:02.771551+00:00
-- url     : https://prove2.me/submissions/841cfca9-b86c-422a-8b0d-07ccee4fcc37

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_stage9P_zero
import Theorems.Thm_O3_stage9P_succ
import Theorems.Thm_O3_stage9P_gradient_eq
import Theorems.Thm_O3_pairing_sub_add_self
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
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
theorem _root_.solution {d : ℕ} {theta : ℕ → ℝ}
    {g : ℕ → Vec d} {k : ℕ} (hθ : theta k ≠ 0) :
    theta k * pairing (stage9P theta g k - g k)
        (stage9P theta g k + stage9P theta g (k + 1)) =
      (theta k) ^ 2 *
        ((lpNorm 2 (stage9P theta g k)) ^ (2 : ℕ) -
          (lpNorm 2 (stage9P theta g (k + 1))) ^ (2 : ℕ)) := by
  have hg := stage9P_gradient_eq (theta := theta) (g := g) hθ
  have hsub : stage9P theta g k - g k =
      theta k • (stage9P theta g k - stage9P theta g (k + 1)) := by
    rw [hg]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, Stage2RouteD.pairing_smul_left,
    pairing_sub_add_self]
  ring
end O3
