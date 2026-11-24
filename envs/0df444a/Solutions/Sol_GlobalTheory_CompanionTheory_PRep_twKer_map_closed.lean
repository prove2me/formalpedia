-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.twKer_map_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:43.329378+00:00
-- url     : https://prove2.me/submissions/2cd90046-24b2-470b-a69b-73b59c8475cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwKerEqMapOfSurjective
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_twKer_eq_map_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep
namespace GlobalTheory.CompanionTheory.PRep
theorem _root_.solution : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f :=
  fun ρ σ N θ f hf hint => GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ σ N θ f hf hint
end GlobalTheory.CompanionTheory.PRep
