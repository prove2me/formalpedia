-- Prove2me | solution 1 for GlobalTheory.MinorNorm.prod_sub_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:34.447082+00:00
-- url     : https://prove2.me/submissions/3bcbe571-189a-4794-808c-296064869746

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
theorem _root_.solution (s t : ℕ) (h : s + 1 ≤ t) :
    ∏ j ∈ Finset.Ico (s + 1) t, ((j : ℚ) - s) = (t - (s + 1)).factorial := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.prod_Ico_succ_top ht, ih, Nat.succ_sub ht, Nat.factorial_succ]
    push_cast [Nat.cast_sub ht]
    ring
end GlobalTheory.MinorNorm
