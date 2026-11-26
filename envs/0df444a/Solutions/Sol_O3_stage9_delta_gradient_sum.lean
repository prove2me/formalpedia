-- Prove2me | solution 1 for O3.stage9_delta_gradient_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:34.087023+00:00
-- url     : https://prove2.me/submissions/a019dc2e-80ea-4251-813e-532adb79f4bc

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
theorem _root_.solution {d : ℕ}
    (N : ℕ) (theta kappa delta : ℕ → ℝ) (g : ℕ → Vec d)
    (hθ : ∀ k, theta k ≠ 0)
    (hδ : ∀ k, k < N → delta k = kappa (k + 1) / theta k)
    (hκ : ∀ k, k < N →
      kappa k = kappa (k + 1) * (1 - 1 / theta k)) :
    ∀ k, k ≤ N → ∑ j ∈ Finset.range k, delta j • g j =
      kappa k • stage9P theta g k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      rw [ih (by omega), hδ k (by omega), hκ k (by omega), stage9P_succ]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hθ k]
end O3
