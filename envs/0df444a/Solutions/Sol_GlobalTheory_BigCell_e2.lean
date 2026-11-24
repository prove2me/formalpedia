-- Prove2me | solution 1 for GlobalTheory.BigCell.e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:29.76615+00:00
-- url     : https://prove2.me/submissions/325fdcf4-33be-4ee9-bde7-81bdc7e4042e

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
theorem _root_.solution : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) =
    (2 : R) • (1 : Matrix (β ⊕ β) (β ⊕ β) R) := by
  rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromBlocks_add, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [two_smul]
end GlobalTheory.BigCell
