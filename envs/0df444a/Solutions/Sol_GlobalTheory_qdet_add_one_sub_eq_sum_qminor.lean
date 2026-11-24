-- Prove2me | solution 1 for GlobalTheory.qdet_add_one_sub_eq_sum_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:33.709525+00:00
-- url     : https://prove2.me/submissions/e4b334cc-4039-4f5e-a923-7d4527b32819

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor
import Theorems.Thm_GlobalTheory_CapelliDiff_qdet_add_one_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
end GlobalTheory
