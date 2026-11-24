-- Prove2me | solution 1 for GlobalTheory.T.exists_valuationRing_dominating_specialization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:43.165798+00:00
-- url     : https://prove2.me/submissions/baa6960b-9c79-4619-906b-f267144ffc6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecialization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecializationStatement
import Theorems.Thm_GlobalTheory_exists_valuationRing_of_specializes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  first | exact @GlobalTheory.exists_valuationRing_of_specializes | exact GlobalTheory.exists_valuationRing_of_specializes | (intros; apply GlobalTheory.exists_valuationRing_of_specializes <;> assumption)
end _root_.GlobalTheory.T
