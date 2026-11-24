-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.vec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:53:47.856122+00:00
-- url     : https://prove2.me/submissions/468a5d28-2889-41ae-9b2d-1b522165bf7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution {f f' : Fin (N + 2) → L} (h0 : f 0 = f' 0) (hm : ∀ j, f (mid j) = f' (mid j))
    (hl : f (Fin.last (N + 1)) = f' (Fin.last (N + 1))) : f = f' := by
  funext j
  rcases idx_cases j with rfl | ⟨k, rfl⟩ | rfl
  exacts [h0, hm k, hl]
end GlobalTheory.InertZeta.RowSpan
