-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.LFunction_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:00.999499+00:00
-- url     : https://prove2.me/submissions/057c8c48-5df3-4c24-9f2a-da8d8594db92

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_hurwitzZeta_zero_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (h0 : Φ 0 = 0)
    (hsum : ∑ j, Φ j = 0) :
    ZMod.LFunction Φ 0 = -(1 / N) * ∑ j : ZMod N, Φ j * (j.val : ℂ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have key : ∀ j : ZMod N, Φ j * hurwitzZeta (ZMod.toAddCircle j) 0 =
      Φ j * (1 / 2 - (j.val : ℂ) / N) := by
    intro j
    by_cases hj : j = 0
    · rw [hj, h0, zero_mul, zero_mul]
    · have hv0 : 0 < j.val := Nat.pos_of_ne_zero fun h ↦ hj ((ZMod.val_eq_zero j).1 h)
      have hvN : j.val < N := ZMod.val_lt j
      rw [ZMod.toAddCircle_apply, hurwitzZeta_zero_eq (div_pos (Nat.cast_pos.2 hv0) hN)
        ((div_lt_one hN).2 (by exact_mod_cast hvN))]
      push_cast
      ring
  rw [ZMod.LFunction, neg_zero, cpow_zero, one_mul, Finset.sum_congr rfl fun j _ ↦ key j]
  have hs : ∑ j : ZMod N, Φ j * (1 / 2 - (j.val : ℂ) / N) =
      (∑ j, Φ j) * (1 / 2) - (1 / N) * ∑ j : ZMod N, Φ j * (j.val : ℂ) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hs, hsum]
  ring
end GroundTheory.Global.Quadratic
