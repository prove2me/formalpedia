-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.map_mem_map_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.004374+00:00
-- url     : https://prove2.me/submissions/474949b5-b433-4329-a713-578d1fbb2ff8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A B : CommRingCat.{u}} {φ : R ⟶ A} {ψ : A ⟶ B} {χ : R ⟶ B}
    (h : φ ≫ ψ = χ) {I : Ideal R} {x : A} (hx : x ∈ I.map φ.hom) : ψ x ∈ I.map χ.hom := by
  rw [← h, CommRingCat.hom_comp, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx
end GlobalTheory.ProperFunctions
