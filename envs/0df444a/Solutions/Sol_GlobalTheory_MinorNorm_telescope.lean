-- Prove2me | solution 1 for GlobalTheory.MinorNorm.telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:27.875813+00:00
-- url     : https://prove2.me/submissions/a60710bd-6c2d-4082-a18f-a4de58adf4e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (c : ℚ) (s t : ℕ) (h : s ≤ t) :
    (∏ j ∈ Finset.Ico s t, (c + 1 + j)) * (c + s) = (∏ j ∈ Finset.Ico s t, (c + j)) * (c + t) := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, Finset.prod_Ico_succ_top ht]
    push_cast
    linear_combination (c + 1 + t) * ih
end GlobalTheory.MinorNorm
