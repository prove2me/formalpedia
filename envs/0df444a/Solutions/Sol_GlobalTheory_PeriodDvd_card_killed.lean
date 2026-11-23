-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.card_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:48.377736+00:00
-- url     : https://prove2.me/submissions/84e818f4-1b04-4ee5-aff3-99bbb579bb1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_killed_eq_image
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
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) : (killed d s).card = s := by
  rw [killed_eq_image h, Finset.card_image_of_injOn (injOn_mul h), Finset.card_range]
end GlobalTheory.PeriodDvd
