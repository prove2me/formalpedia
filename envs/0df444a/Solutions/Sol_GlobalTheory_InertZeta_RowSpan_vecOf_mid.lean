-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.vecOf_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:15:27.048245+00:00
-- url     : https://prove2.me/submissions/18a9fe43-04e8-4a3b-960a-38b97cc4b964

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
theorem _root_.solution (x₀ : L) (xm : Fin N → L) (xl : L) (k : Fin N) : vecOf x₀ xm xl (mid k) = xm k := by
  rw [vecOf, mid, Fin.cases_succ, Fin.lastCases_castSucc]
end GlobalTheory.InertZeta.RowSpan
