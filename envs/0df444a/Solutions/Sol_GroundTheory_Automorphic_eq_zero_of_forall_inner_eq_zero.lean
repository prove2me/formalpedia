-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_zero_of_forall_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.690734+00:00
-- url     : https://prove2.me/submissions/e373a6b9-af93-482d-b87b-595ef61c7817

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
namespace GroundTheory.Automorphic
theorem _root_.solution {s : Set X} (hs : span ℝ s = ⊤) {y : X}
    (hy : ∀ x ∈ s, ⟪y, x⟫ = 0) : y = 0 := by
  have hle : span ℝ s ≤ LinearMap.ker (innerSL ℝ y).toLinearMap :=
    span_le.2 fun x hx => by simpa using hy x hx
  have hy' : y ∈ LinearMap.ker (innerSL ℝ y).toLinearMap := hle (hs ▸ mem_top)
  simpa using hy'
end GroundTheory.Automorphic
