-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.rowsP_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:54:05.839998+00:00
-- url     : https://prove2.me/submissions/667abd83-7188-4d95-878f-1bfa24e78962

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
theorem _root_.solution (k : Fin N) : rowsP a g U V y (mid k) = rowM g U V k := by
  rw [rowsP, mid, Fin.cases_succ, Fin.lastCases_castSucc]
end GlobalTheory.InertZeta.RowSpan
