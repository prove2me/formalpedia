-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.sum_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:54.008112+00:00
-- url     : https://prove2.me/submissions/5098c121-4b70-4380-831c-b8991e5f59fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_killed_eq_image
import Theorems.Thm_GlobalTheory_PeriodDvd_val_mul
import Theorems.Thm_GlobalTheory_PeriodDvd_injOn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) (q : ℕ) :
    ∑ x ∈ killed d s, q ^ x.val = ∑ j ∈ Finset.range s, (q ^ e) ^ j := by
  rw [killed_eq_image h, Finset.sum_image (injOn_mul h)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [val_mul h (Finset.mem_range.mp hj), pow_mul]
end GlobalTheory.PeriodDvd
