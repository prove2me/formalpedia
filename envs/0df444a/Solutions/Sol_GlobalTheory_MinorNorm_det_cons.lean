-- Prove2me | solution 1 for GlobalTheory.MinorNorm.det_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:35.353302+00:00
-- url     : https://prove2.me/submissions/eb9fd8cd-4105-4f7c-aa9a-695d2461b180

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
variable {R : Type} [CommRing R] [Algebra ℂ R]
namespace GlobalTheory.MinorNorm
theorem _root_.solution {m : ℕ} (v : Fin (m + 1) → R) (M : Fin m → Fin (m + 1) → R) :
    (Matrix.of (Fin.cons v M : Fin (m + 1) → Fin (m + 1) → R)).det =
      ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * v s * (Matrix.of fun t u => M t (s.succAbove u)).det := by
  rw [det_succ_row_zero]
  rfl
end GlobalTheory.MinorNorm
