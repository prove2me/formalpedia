-- Prove2me | solution 1 for GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:33.711491+00:00
-- url     : https://prove2.me/submissions/6f7b2f82-ca6d-4dbc-95a0-4a5a1e8c067a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMulStatement
import Theorems.Thm_GlobalTheory_finsum_comp_eq_finsum_natCard_fiber_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  first | exact @GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | exact GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | (intros; apply GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul <;> assumption)
end _root_.GlobalTheory.T
