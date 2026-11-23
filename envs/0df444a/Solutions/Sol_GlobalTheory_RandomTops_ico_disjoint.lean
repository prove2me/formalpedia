-- Prove2me | solution 1 for GlobalTheory.RandomTops.ico_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:01.54492+00:00
-- url     : https://prove2.me/submissions/11620110-0f43-4ad9-b630-f79e0da61ea1

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution {a m i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ico (a + i * m) (a + (i + 1) * m)) (Finset.Ico (a + j * m) (a + (j + 1) * m)) := by
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (i + 1) * m ≤ j * m := Nat.mul_le_mul_right m h
    omega
  · have : (j + 1) * m ≤ i * m := Nat.mul_le_mul_right m h
    omega
end GlobalTheory.RandomTops
