-- Prove2me | solution 1 for GlobalTheory.range_subset_of_closedPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:36.536807+00:00
-- url     : https://prove2.me/submissions/985be911-76cf-462b-82b7-802fda1a759d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

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
theorem _root_.solution (f : Spec (.of R) ⟶ X) {U : X.Opens}
    (hU : f (closedPoint R) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨y, rfl⟩
  have : y ∈ f ⁻¹ᵁ U := by
    rw [Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) f hU]; trivial
  exact this
end GlobalTheory
