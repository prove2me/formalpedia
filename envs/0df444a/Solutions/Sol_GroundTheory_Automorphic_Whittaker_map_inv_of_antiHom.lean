-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.map_inv_of_antiHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:30.315691+00:00
-- url     : https://prove2.me/submissions/01e143fe-c3ae-4fda-b46e-71303ecddffd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
omit [IsTopologicalGroup G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (σ : G ≃ₜ G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (x : G) :
    σ x⁻¹ = (σ x)⁻¹ := by
  have h1 : σ 1 = 1 := by
    have := hσ 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  rw [eq_inv_iff_mul_eq_one, ← hσ, mul_inv_cancel, h1]
end GroundTheory.Automorphic.Whittaker
