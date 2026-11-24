-- Prove2me | solution 1 for GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:07.027923+00:00
-- url     : https://prove2.me/submissions/d44b17b4-8f4d-42bd-b62c-0648ac2dcd5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMemStatement
import Theorems.Thm_GlobalTheory_isAdicComplete_of_fg_of_natCast_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by
  first | exact @GlobalTheory.isAdicComplete_of_fg_of_natCast_mem | exact GlobalTheory.isAdicComplete_of_fg_of_natCast_mem | (intros; apply GlobalTheory.isAdicComplete_of_fg_of_natCast_mem <;> assumption)
end _root_.GlobalTheory.T
