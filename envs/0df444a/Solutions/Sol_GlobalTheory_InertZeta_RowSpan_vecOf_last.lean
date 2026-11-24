-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.vecOf_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:15.037006+00:00
-- url     : https://prove2.me/submissions/91fc36ba-cddc-4117-81a5-79e9f75df028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis

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
theorem _root_.solution (x₀ : L) (xm : Fin N → L) (xl : L) : vecOf x₀ xm xl (Fin.last (N + 1)) = xl := by
  rw [vecOf, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]
end GlobalTheory.InertZeta.RowSpan
