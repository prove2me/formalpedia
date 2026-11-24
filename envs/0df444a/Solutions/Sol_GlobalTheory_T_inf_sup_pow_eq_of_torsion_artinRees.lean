-- Prove2me | solution 1 for GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:07.79339+00:00
-- url     : https://prove2.me/submissions/0dbaa5b7-c87d-4812-adfd-f4cb100d5f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfSupPowEqOfTorsionArtinRees
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfSupPowEqOfTorsionArtinReesStatement
import Theorems.Thm_GlobalTheory_inf_sup_pow_eq_of_torsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.inf_sup_pow_eq_of_torsion | exact GlobalTheory.inf_sup_pow_eq_of_torsion | (intros; apply GlobalTheory.inf_sup_pow_eq_of_torsion <;> assumption)
end _root_.GlobalTheory.T
