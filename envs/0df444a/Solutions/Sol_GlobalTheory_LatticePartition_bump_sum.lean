-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bump_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:39:58.577173+00:00
-- url     : https://prove2.me/submissions/9225a36f-6bd5-4873-9a42-bc90f6aabf4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
namespace GlobalTheory.LatticePartition
theorem _root_.solution (y : ℝ) : ∑ k ∈ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ), bump (y - k) = 1 := by
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have e1 : y - ((⌊y⌋ - 1 : ℤ) : ℝ) = y - (⌊y⌋ : ℝ) + 1 := by push_cast; ring
  have e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) + 1 = y - (⌊y⌋ : ℝ) := by push_cast; ring
  have ha : Real.smoothTransition (y - (⌊y⌋ : ℝ) + 1 + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hb : Real.smoothTransition (y - ((⌊y⌋ + 1 : ℤ) : ℝ)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)
  unfold bump
  rw [e1, e2, ha, hb]
  ring
end GlobalTheory.LatticePartition
