-- Prove2me | solution 1 for GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:42.056347+00:00
-- url     : https://prove2.me/submissions/befc0e8a-c384-4836-9b57-3c559d58c8aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSource
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSourceStatement
import Theorems.Thm_GlobalTheory_exists_factor_closedImmersion_of_locally


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z), (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) → ∃ z : Y ⟶ A, z ≫ a = g := by
  first | exact @GlobalTheory.exists_factor_closedImmersion_of_locally | exact GlobalTheory.exists_factor_closedImmersion_of_locally | (intros; apply GlobalTheory.exists_factor_closedImmersion_of_locally <;> assumption)
end _root_.GlobalTheory.T
