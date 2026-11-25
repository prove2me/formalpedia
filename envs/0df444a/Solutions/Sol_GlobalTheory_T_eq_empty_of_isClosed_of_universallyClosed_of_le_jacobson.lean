-- Prove2me | solution 1 for GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:17.961868+00:00
-- url     : https://prove2.me/submissions/c9f744e2-5de0-4982-8c32-e773d57d39c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedEmptyOfUniversallyClosedOfLeJacobson
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedEmptyOfUniversallyClosedOfLeJacobsonStatement
import Theorems.Thm_GlobalTheory_closed_empty_of_universallyClosed_of_le_jacobson


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  first | exact @GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | exact GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson | (intros; apply GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson <;> assumption)
end _root_.GlobalTheory.T
