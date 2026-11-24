-- Prove2me | solution 1 for GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:09:23.971649+00:00
-- url     : https://prove2.me/submissions/72b26c97-3910-4d30-8ecb-2c83dfa212ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
import Theorems.Thm_GlobalTheory_irreducible_idempotent_eq_one_and_character_eq_weight


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
theorem _root_.solution : ∀ (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V), ρ.IsIrreducible → (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧ (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) → ∀ g, ρ.character g = (lam g : L)) := by
  first | exact @GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | exact GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | (intros; apply GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight <;> assumption)
end _root_.GlobalTheory.T
