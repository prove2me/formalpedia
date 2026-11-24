-- Prove2me | solution 1 for GlobalTheory.MinorNorm.addCol_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:32.196493+00:00
-- url     : https://prove2.me/submissions/466ebb9e-72f4-4092-9070-6dbb5223727d

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
theorem _root_.solution {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) : Antitone (addCol a K) := by
  intro i j hij
  have := ha hij
  unfold addCol
  by_cases h : j ≤ K
  · rw [if_pos h, if_pos (hij.trans h)]; omega
  · rw [if_neg h]; omega
end GlobalTheory.MinorNorm
