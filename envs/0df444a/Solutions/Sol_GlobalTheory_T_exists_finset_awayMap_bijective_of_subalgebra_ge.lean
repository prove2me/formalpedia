-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:04.452237+00:00
-- url     : https://prove2.me/submissions/20f606ea-9598-44ce-90a2-995403e28ed4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Theorems.Thm_GlobalTheory_exists_finset_awayMap_subalgebra_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  first | exact @GlobalTheory.exists_finset_awayMap_subalgebra_bijective | exact GlobalTheory.exists_finset_awayMap_subalgebra_bijective | (intros; apply GlobalTheory.exists_finset_awayMap_subalgebra_bijective <;> assumption)
end _root_.GlobalTheory.T
