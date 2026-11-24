-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bump_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:45.232441+00:00
-- url     : https://prove2.me/submissions/01edb389-ef99-4518-ad4d-f1bc5af33c6f

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
theorem _root_.solution {t : ℝ} (h : 1 ≤ |t|) : bump t = 0 := by
  unfold bump
  rcases le_abs'.1 h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h]
    simp
end GlobalTheory.LatticePartition
