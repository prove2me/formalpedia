-- Prove2me | solution 1 for GroundTheory.LocalField.comp_conjNormal_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:20.469848+00:00
-- url     : https://prove2.me/submissions/1149dfb9-0f13-4165-96d8-242458553413

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
namespace GroundTheory.LocalField
theorem _root_.solution (θ : A → ℂ) (g h : G) :
    θ ∘ conjNormal A h = θ ∘ conjNormal A g ↔ g⁻¹ * h ∈ inertia A θ := by
  constructor
  · intro e b
    obtain ⟨a, rfl⟩ := (conjNormal A g).surjective b
    rw [← conjNormal_mul, mul_inv_cancel_left]
    exact congrFun e a
  · intro hx
    funext a
    have hh : h = g * (g⁻¹ * h) := by group
    simp only [Function.comp_apply]
    rw [hh, conjNormal_mul]
    exact hx _
end GroundTheory.LocalField
