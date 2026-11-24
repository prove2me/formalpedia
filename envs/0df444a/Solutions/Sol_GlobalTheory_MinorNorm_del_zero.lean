-- Prove2me | solution 1 for GlobalTheory.MinorNorm.del_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:34.509495+00:00
-- url     : https://prove2.me/submissions/e8ea7b71-07f5-4a4d-ab25-808b587dd6f5

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
variable {σ : Type} (v : Fin l → Fin l → σ)
namespace GlobalTheory.MinorNorm
theorem _root_.solution : del v 0 = 1 := by simp [del]
end GlobalTheory.MinorNorm
