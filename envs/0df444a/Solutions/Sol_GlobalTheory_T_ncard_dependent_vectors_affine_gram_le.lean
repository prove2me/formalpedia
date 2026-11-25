-- Prove2me | solution 1 for GlobalTheory.T.ncard_dependent_vectors_affine_gram_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:03.287845+00:00
-- url     : https://prove2.me/submissions/4cc5a049-3c2a-4c94-a33f-7105541f8995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLeStatement
import Theorems.Thm_GlobalTheory_GramCount_ncard_dependent_le


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
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B), Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_dependent_le | exact GlobalTheory.GramCount.ncard_dependent_le | (intros; apply GlobalTheory.GramCount.ncard_dependent_le <;> assumption)
end _root_.GlobalTheory.T
