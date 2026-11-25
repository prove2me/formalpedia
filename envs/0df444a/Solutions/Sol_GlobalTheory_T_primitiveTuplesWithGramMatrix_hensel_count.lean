-- Prove2me | solution 1 for GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:21.133675+00:00
-- url     : https://prove2.me/submissions/4a91514b-2163-4acf-b85a-c283d343b20a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Theorems.Thm_GlobalTheory_GramCount_hensel_count


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
theorem _root_.solution : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  first | exact @GlobalTheory.GramCount.hensel_count | exact GlobalTheory.GramCount.hensel_count | (intros; apply GlobalTheory.GramCount.hensel_count <;> assumption)
end _root_.GlobalTheory.T
