-- Prove2me | solution 1 for GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:57.366474+00:00
-- url     : https://prove2.me/submissions/d30e2064-fab7-4193-858d-9856fc3d3885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
import Theorems.Thm_GlobalTheory_GramCount_ncard_gram_mod_eq_card_ker_pow_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [Finite A] [CommRing B] (c : A →+* A) (c' : B →+* B), (∀ u, c (c u) = u) → ∀ (p : A), IsNilpotent p → ∀ (φ : A →+* B), Function.Surjective φ → (∀ u, φ (c u) = c' (φ u)) → (∀ u, φ u = 0 ↔ p ∣ u) → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} = Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by
  first | exact @GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | exact GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | (intros; apply GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul <;> assumption)
end _root_.GlobalTheory.T
