-- Prove2me | solution 1 for GlobalTheory.T.card_primitiveTuple_extensions_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:09.332805+00:00
-- url     : https://prove2.me/submissions/9982bec8-f914-471c-9047-ae8e5565ae1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLeStatement
import Theorems.Thm_GlobalTheory_GramCount_ncard_extend_prim_one


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
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_extend_prim_one | exact GlobalTheory.GramCount.ncard_extend_prim_one | (intros; apply GlobalTheory.GramCount.ncard_extend_prim_one <;> assumption)
end _root_.GlobalTheory.T
