-- Prove2me | solution 1 for GlobalTheory.exists_isAffineOpen_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:54.274006+00:00
-- url     : https://prove2.me/submissions/2d47f69f-739d-4d68-86b6-6d309411fb06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (x : X) {O : X.Opens} (hx : x ∈ O) :
    ∃ (U : S.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ f ⁻¹ᵁ U ∧ V ≤ O ∧
      x ∈ V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((O ⊓ f ⁻¹ᵁ U : X.Opens) : Set X) from ⟨hx, hxU⟩) (O ⊓ f ⁻¹ᵁ U).isOpen
  exact ⟨U, V, hU, hV, fun y hy => (hVle hy).2, fun y hy => (hVle hy).1, hxV⟩
end _root_.GlobalTheory
end GlobalTheory
