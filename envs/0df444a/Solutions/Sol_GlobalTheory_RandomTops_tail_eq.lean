-- Prove2me | solution 1 for GlobalTheory.RandomTops.tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:11.808969+00:00
-- url     : https://prove2.me/submissions/51eaa446-dc92-45e2-a943-b579d22a7e4f

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
theorem _root_.solution (B : Finset ℕ) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) = binUpper B.card δ K := by
  unfold ex binUpper
  have hs := sum_powerset_apply_card (fun m => δ ^ m * (1 - δ) ^ (#B - m) * ind (K ≤ m)) (x := B)
  rw [hs]
  have hI : Icc K #B = (range (#B + 1)).filter (fun m => K ≤ m) := by
    ext m
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [hI, sum_filter]
  refine sum_congr rfl fun m _ => ?_
  unfold ind
  split_ifs
  · rw [nsmul_eq_mul]
    ring
  · simp
end GlobalTheory.RandomTops
