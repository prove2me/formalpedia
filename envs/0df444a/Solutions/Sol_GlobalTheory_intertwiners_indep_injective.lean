-- Prove2me | solution 1 for GlobalTheory.intertwiners_indep_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:06:16.043976+00:00
-- url     : https://prove2.me/submissions/6a22c2f6-2e34-4bb6-89a9-a6b93637c36c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwiners
import Theorems.Thm_GlobalTheory_intertwiner_sum_eq_zero_imp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Representation
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab
  have := intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b)
    (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  exact sub_eq_zero.mp this
end GlobalTheory
