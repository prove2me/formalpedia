-- Prove2me | solution 1 for GlobalTheory.T.adicCompletion_map_injective_and_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:48.274815+00:00
-- url     : https://prove2.me/submissions/bd1cbffc-ba0c-47eb-8d1c-2555684bef21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariantsStatement
import Theorems.Thm_GlobalTheory_adicCompletion_map_invariants


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first | exact @GlobalTheory.adicCompletion_map_invariants | exact GlobalTheory.adicCompletion_map_invariants | (intros; apply GlobalTheory.adicCompletion_map_invariants <;> assumption)
end _root_.GlobalTheory.T
