-- Prove2me | solution 1 for GlobalTheory.T.torsion_count_multiplicative_prime_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:15.900833+00:00
-- url     : https://prove2.me/submissions/4e536a12-daf6-4b8f-b534-975f271ffe8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowersStatement
import Theorems.Thm_GlobalTheory_card_primaryTorsion_mul_blocks


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
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  first | exact @GlobalTheory.card_primaryTorsion_mul_blocks | exact GlobalTheory.card_primaryTorsion_mul_blocks | (intros; apply GlobalTheory.card_primaryTorsion_mul_blocks <;> assumption)
end _root_.GlobalTheory.T
