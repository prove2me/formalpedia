-- Prove2me | solution 1 for GlobalTheory.DI.delta_Dtot_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:34.175573+00:00
-- url     : https://prove2.me/submissions/a075f15f-29ef-47bf-b240-32139e8c9f97

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
import Theorems.Thm_GlobalTheory_DI_delta_add
import Theorems.Thm_GlobalTheory_DI_delta_sub
import Theorems.Thm_GlobalTheory_DI_delta_delta
import Theorems.Thm_GlobalTheory_DI_Dtot_add
import Theorems.Thm_GlobalTheory_DI_Dtot_sub
import Theorems.Thm_GlobalTheory_DI_Dtot_Dtot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E),
    (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧
    (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧
    (∀ c : Finset ι → E, delta (delta c) = 0) ∧
    ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) :=
  fun d => ⟨delta_add, delta_sub, Dtot_add d, Dtot_sub d, delta_delta, fun hd => Dtot_Dtot d hd⟩
end GlobalTheory.DI
