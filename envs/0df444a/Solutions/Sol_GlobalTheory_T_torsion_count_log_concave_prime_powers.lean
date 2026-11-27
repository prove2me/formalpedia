-- Prove2me | solution 1 for GlobalTheory.T.torsion_count_log_concave_prime_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:12.507588+00:00
-- url     : https://prove2.me/submissions/51afe74c-fd7d-4653-8cb8-b761188fe97e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowersStatement
import Theorems.Thm_GlobalTheory_card_torsion_pow_log_concave


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  first | exact @GlobalTheory.card_torsion_pow_log_concave | exact GlobalTheory.card_torsion_pow_log_concave | (intros; apply GlobalTheory.card_torsion_pow_log_concave <;> assumption)
end _root_.GlobalTheory.T
