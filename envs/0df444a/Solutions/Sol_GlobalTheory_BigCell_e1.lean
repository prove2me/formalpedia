-- Prove2me | solution 1 for GlobalTheory.BigCell.e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:29.193781+00:00
-- url     : https://prove2.me/submissions/386f28d3-5a43-4b04-b130-48875e064cb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.BigCell
theorem _root_.solution : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = 0 := by
  simp [fromCols_mul_fromRows]
end GlobalTheory.BigCell
