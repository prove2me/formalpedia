-- Prove2me | solution 1 for GlobalTheory.T.sum_prod_of_local_choices_bijection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:25.145148+00:00
-- url     : https://prove2.me/submissions/812881de-4bc4-4488-97f7-740e08381fd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumProdOfLocalChoicesBijection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumProdOfLocalChoicesBijectionStatement
import Theorems.Thm_GlobalTheory_prod_sum_of_local_choices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)] (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p)), (∀ p ∈ s, (U p).Finite) → (∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c') → (∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p) → (∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p) → ∀ g : ∀ p, O p → R, Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  first | exact @GlobalTheory.prod_sum_of_local_choices | exact GlobalTheory.prod_sum_of_local_choices | (intros; apply GlobalTheory.prod_sum_of_local_choices <;> assumption)
end _root_.GlobalTheory.T
