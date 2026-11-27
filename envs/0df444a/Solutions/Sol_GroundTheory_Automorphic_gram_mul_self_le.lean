-- Prove2me | solution 1 for GroundTheory.Automorphic.gram_mul_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:55.861829+00:00
-- url     : https://prove2.me/submissions/35608f24-40b9-4584-be6d-51b6943f77bc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction

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
open Module Matrix Submodule
open scoped RealInnerProductSpace
variable {J : Type*} [Fintype J]
namespace GroundTheory.Automorphic
theorem _root_.solution (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (x y : J → ℝ) :
    (x ⬝ᵥ (G *ᵥ y)) * (x ⬝ᵥ (G *ᵥ y)) ≤ (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) := by
  let core := gramCore G hs hpos
  let _ : NormedAddCommGroup (GramSpace G) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (GramSpace G) := .ofCore _
  exact real_inner_mul_inner_self_le (toGram G x) (toGram G y)
end GroundTheory.Automorphic
