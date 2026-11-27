-- Prove2me | solution 1 for GlobalTheory.T.injective_sum_of_linIndep_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:09:16.354942+00:00
-- url     : https://prove2.me/submissions/092121c4-4834-4935-b358-0134833a58d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwiners
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwinersStatement
import Theorems.Thm_GlobalTheory_intertwiners_indep_injective


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
theorem _root_.solution : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  first | exact @GlobalTheory.intertwiners_indep_injective | exact GlobalTheory.intertwiners_indep_injective | (intros; apply GlobalTheory.intertwiners_indep_injective <;> assumption)
end _root_.GlobalTheory.T
