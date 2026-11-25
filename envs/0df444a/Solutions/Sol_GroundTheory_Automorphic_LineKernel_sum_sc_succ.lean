-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.sum_sc_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:22.692801+00:00
-- url     : https://prove2.me/submissions/1a32efd3-9e43-4adb-97a7-fe23ae036f67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_zero_right
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℂ) :
    ∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * d p =
      ∑ p ∈ Finset.range (n + 1), sc a n p * d p -
        (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * d (p + 1) := by
  have key : ∀ p, sc a (n + 1) (p + 1) * d (p + 1) =
      sc a n (p + 1) * d (p + 1) - (a n : ℂ)⁻¹ * (sc a n p * d (p + 1)) := by
    intro p; simp only [sc, coef]; push_cast; ring
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ _ n,
    Finset.sum_range_succ' (fun p => sc a n p * d p) n,
    Finset.sum_range_succ (fun p => sc a n p * d (p + 1)) n,
    Finset.sum_congr rfl (fun p _ => key p), Finset.sum_sub_distrib, ← Finset.mul_sum, key n]
  have h1 : sc a n (n + 1) = 0 := by simp [sc, coef_eq_zero a (Nat.lt_succ_self n)]
  have h2 : sc a (n + 1) 0 = sc a n 0 := by simp [sc, coef_zero_right]
  rw [h1, h2]
  ring
end GroundTheory.Automorphic.LineKernel
