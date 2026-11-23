-- Prove2me | solution 1 for GlobalTheory.DirichletTail.norm_boundary_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:27.335875+00:00
-- url     : https://prove2.me/submissions/865ff49f-2d16-4483-99de-cd7d04068e95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_norm_sum_range_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (N : ℕ) :
    ‖(∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖
      ≤ q * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos (Nat.succ_pos N), Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (norm_sum_range_le χ hχ N) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
end GlobalTheory.DirichletTail
