-- Prove2me | solution 1 for GlobalTheory.nsmul_surj_of_card_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:28.937238+00:00
-- url     : https://prove2.me/submissions/2e8e8647-ab5d-4609-a119-3cb682ddfac1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionLiftNumberFieldModule
import Theorems.Thm_GlobalTheory_nsmul_surjective_torsion_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  intro F _ _ M _ _ N hN h j y hy
  exact nsmul_surjective_torsion_lift M N _ hN h j y hy
end GlobalTheory
