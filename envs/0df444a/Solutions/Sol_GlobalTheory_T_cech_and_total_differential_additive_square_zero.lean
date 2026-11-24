-- Prove2me | solution 1 for GlobalTheory.T.cech_and_total_differential_additive_square_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:20.585808+00:00
-- url     : https://prove2.me/submissions/f383674d-5e39-4ad8-8d12-6f92eda0f17a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZeroStatement
import Theorems.Thm_GlobalTheory_DI_delta_Dtot_props


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E), (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧ (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧ (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧ (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧ (∀ c : Finset ι → E, delta (delta c) = 0) ∧ ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) := by
  first | exact @GlobalTheory.DI.delta_Dtot_props | exact GlobalTheory.DI.delta_Dtot_props | (intros; apply GlobalTheory.DI.delta_Dtot_props <;> assumption)
end _root_.GlobalTheory.T
