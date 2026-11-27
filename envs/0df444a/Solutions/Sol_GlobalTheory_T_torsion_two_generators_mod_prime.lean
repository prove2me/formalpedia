-- Prove2me | solution 1 for GlobalTheory.T.torsion_two_generators_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:24.394819+00:00
-- url     : https://prove2.me/submissions/9de58ed5-5d2b-46fe-96e1-94a5302ec134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsModPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsModPrimeStatement
import Theorems.Thm_GlobalTheory_torsionBy_two_generators_mod_prime


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  first | exact @GlobalTheory.torsionBy_two_generators_mod_prime | exact GlobalTheory.torsionBy_two_generators_mod_prime | (intros; apply GlobalTheory.torsionBy_two_generators_mod_prime <;> assumption)
end _root_.GlobalTheory.T
