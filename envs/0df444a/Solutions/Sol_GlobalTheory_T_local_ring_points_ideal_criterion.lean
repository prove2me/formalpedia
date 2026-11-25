-- Prove2me | solution 1 for GlobalTheory.T.local_ring_points_ideal_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:36.054495+00:00
-- url     : https://prove2.me/submissions/ecde12e1-9712-4144-80ea-d4096ab1c392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterionStatement
import Theorems.Thm_GlobalTheory_factor_closedImmersion_iff_of_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  first | exact @GlobalTheory.factor_closedImmersion_iff_of_local | exact GlobalTheory.factor_closedImmersion_iff_of_local | (intros; apply GlobalTheory.factor_closedImmersion_iff_of_local <;> assumption)
end _root_.GlobalTheory.T
