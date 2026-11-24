-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.smem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:58.374938+00:00
-- url     : https://prove2.me/submissions/840f7632-50bc-4612-baf5-870581e83368

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
theorem _root_.solution {n : ℕ} {S : Submodule (intL L) (Fin n → L)} {x : L} {w : Fin n → L} (hx : x ∈ intL L) (hw : w ∈ S) :
    x • w ∈ S := S.smul_mem ⟨x, hx⟩ hw
end GlobalTheory.InertZeta.RowSpan
