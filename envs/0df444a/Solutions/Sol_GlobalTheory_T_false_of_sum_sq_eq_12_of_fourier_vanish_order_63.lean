-- Prove2me | solution 1 for GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:08.981658+00:00
-- url     : https://prove2.me/submissions/e8836bbb-01c1-4abf-9eac-27182c32988a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythreeStatement
import Theorems.Thm_GlobalTheory_no_norm_twelve_order_sixtythree


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
theorem _root_.solution : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
end _root_.GlobalTheory.T
