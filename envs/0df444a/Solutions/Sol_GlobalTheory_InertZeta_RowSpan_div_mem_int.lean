-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.div_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:55.714829+00:00
-- url     : https://prove2.me/submissions/6a1fb63a-967f-4e0d-aeca-74eac64e81ff

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
theorem _root_.solution {x y : L} (h : Valued.v x ≤ Valued.v y) : x / y ∈ intL L := by
  show Valued.v (x / y) ≤ 1
  rw [map_div₀]
  exact div_le_one_of_le₀ h zero_le'
end GlobalTheory.InertZeta.RowSpan
