-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.rowsP_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:56.83885+00:00
-- url     : https://prove2.me/submissions/39b8db6e-003d-45e1-8279-edba55d23f66

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
variable (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L)
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution : rowsP a g U V y 0 = if 0 ≤ a then (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 else g 0 := by
  rw [rowsP, Fin.cases_zero]
end GlobalTheory.InertZeta.RowSpan
