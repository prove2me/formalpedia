-- Prove2me | solution 1 for GlobalTheory.isLocalHom_of_factor_completedStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:38.10482+00:00
-- url     : https://prove2.me/submissions/c7bbb300-42a0-4bfd-9242-0a36abde7b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_isLocalHom_of_extend_adicCompletion
import Theorems.Thm_GlobalTheory_isLocalHom_of_factor_stalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution {f : Spec (.of R) ⟶ X} {x : X}
    (hx : f (closedPoint R) = x) (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    {ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R}
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f) : IsLocalHom ψ := by
  rw [fromSpecCompletedStalk, ← Spec.map_comp_assoc] at hψ
  exact isLocalHom_of_extend_adicCompletion hfg ψ (hψ := isLocalHom_of_factor_stalk hx hψ)
end GlobalTheory
