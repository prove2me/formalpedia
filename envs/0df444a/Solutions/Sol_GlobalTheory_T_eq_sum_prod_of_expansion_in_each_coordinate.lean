-- Prove2me | solution 1 for GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:57.912276+00:00
-- url     : https://prove2.me/submissions/f7c79053-a5d6-4949-99a0-56ed61f670ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExpandPiOfExpandEach
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExpandPiOfExpandEachStatement
import Theorems.Thm_GlobalTheory_expand_pi_of_expand_each


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
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  first | exact @GlobalTheory.expand_pi_of_expand_each | exact GlobalTheory.expand_pi_of_expand_each | (intros; apply GlobalTheory.expand_pi_of_expand_each <;> assumption)
end _root_.GlobalTheory.T
