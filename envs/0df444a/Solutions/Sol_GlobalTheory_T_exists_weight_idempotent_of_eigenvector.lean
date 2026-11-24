-- Prove2me | solution 1 for GlobalTheory.T.exists_weight_idempotent_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:01.500295+00:00
-- url     : https://prove2.me/submissions/6bcbf1dc-8f23-41cd-86f1-f7f0f9f9d94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotentStatement
import Theorems.Thm_GlobalTheory_exists_weight_idempotent


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
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G) (lam : B →* Lˣ) (v : V), B.Normal → v ≠ 0 → (∀ b : B, ρ b v = (lam b : L) • v) → (∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) → ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧ (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  first | exact @GlobalTheory.exists_weight_idempotent | exact GlobalTheory.exists_weight_idempotent | (intros; apply GlobalTheory.exists_weight_idempotent <;> assumption)
end _root_.GlobalTheory.T
