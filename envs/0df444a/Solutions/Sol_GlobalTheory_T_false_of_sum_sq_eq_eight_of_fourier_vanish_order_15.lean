-- Prove2me | solution 1 for GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:21.426409+00:00
-- url     : https://prove2.me/submissions/28f66524-5a2d-4c42-a67b-26ea233b706c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteenStatement
import Theorems.Thm_GlobalTheory_no_norm_eight_of_fourier_vanishing_order_fifteen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | exact GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | (intros; apply GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen <;> assumption)
end _root_.GlobalTheory.T
