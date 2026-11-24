-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.hasSum_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:38.713302+00:00
-- url     : https://prove2.me/submissions/b6637a0e-8c0f-432f-bd59-934124e47681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_rowError
import Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun m : ℤ => rowSum (m * x) (m * y) s)
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h1 : Summable fun n : ℕ => (n + 1 : ℝ) ^ (1 - 2 * s) := by
    exact_mod_cast (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.2 (show 1 - 2 * s < -1 by linarith))
  have h2 : HasSum (fun m : ℕ => rowSum ((m + 1) * x) ((m + 1) * y) s)
      ((∑' m, rowError x y m s)
        + (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
    refine ((summable_rowError x hy hs.le).hasSum.add (h1.hasSum.mul_left _)).congr_fun fun m => ?_
    rw [rowError, Real.mul_rpow (by positivity) hy.le]
    ring
  have h3 := HasSum.of_add_one_of_neg_add_one (f := fun m : ℤ => rowSum (m * x) (m * y) s)
    (h2.congr_fun fun m => by push_cast; rfl)
    (h2.congr_fun fun m => by push_cast; rw [neg_mul, neg_mul, rowSum_neg])
  convert h3 using 1
  simp
  ring
end GlobalTheory.KroneckerLimit
