-- Prove2me | solution 1 for GlobalTheory.sum_prod_box_erase_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:06.791848+00:00
-- url     : https://prove2.me/submissions/040dba77-4a63-40d9-bb25-f56a0b99225c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDyadicShellIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ (Fintype.piFinset (fun _ : ι => range (N + 1))).erase (fun _ => 0), ∏ v, W (k v)
      = (W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι := by
  classical
  have hz : (fun _ : ι => (0 : ℕ)) ∈ Fintype.piFinset (fun _ : ι => range (N + 1)) := by
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_erase_eq_sub hz,
    ← Finset.prod_univ_sum (fun _ : ι => range (N + 1)) (fun _ j => W j),
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.sum_range_succ', add_comm]
end GlobalTheory
