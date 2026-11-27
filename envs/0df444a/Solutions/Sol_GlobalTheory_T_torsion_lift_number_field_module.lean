-- Prove2me | solution 1 for GlobalTheory.T.torsion_lift_number_field_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:22.810397+00:00
-- url     : https://prove2.me/submissions/f907d697-744b-4a67-9108-bfa8cbcdd479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionLiftNumberFieldModule
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionLiftNumberFieldModuleStatement
import Theorems.Thm_GlobalTheory_nsmul_surj_of_card_torsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  first | exact @GlobalTheory.nsmul_surj_of_card_torsion | exact GlobalTheory.nsmul_surj_of_card_torsion | (intros; apply GlobalTheory.nsmul_surj_of_card_torsion <;> assumption)
end _root_.GlobalTheory.T
