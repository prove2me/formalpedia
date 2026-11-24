-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.zero_ne_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:54.816797+00:00
-- url     : https://prove2.me/submissions/9c9e7f95-446d-466f-bd75-bfc825d2d4a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero


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
theorem _root_.solution (j : Fin N) : (0 : Fin (N + 2)) ≠ mid j := (mid_ne_zero j).symm
end GlobalTheory.InertZeta.RowSpan
