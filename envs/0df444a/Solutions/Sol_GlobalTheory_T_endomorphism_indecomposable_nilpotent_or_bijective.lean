-- Prove2me | solution 1 for GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:48.091926+00:00
-- url     : https://prove2.me/submissions/997dd0dd-d01a-43b7-86ea-5976362755f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijectiveStatement
import Theorems.Thm_GlobalTheory_endo_indecomposable_finite_length_nilpotent_or_bijective


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
theorem _root_.solution : ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) → ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  first | exact @GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | exact GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | (intros; apply GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective <;> assumption)
end _root_.GlobalTheory.T
