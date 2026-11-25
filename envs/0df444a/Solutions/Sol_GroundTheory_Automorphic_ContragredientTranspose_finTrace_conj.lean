-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.finTrace_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:23.310025+00:00
-- url     : https://prove2.me/submissions/f01c87cc-a015-41d3-b339-08e31e4c946a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character

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
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (e : V ≃ₗ[ℂ] V) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (e.conj T) = finTrace T := by
  set R := LinearMap.range T
  have hE : LinearMap.range (e.conj T) ≤ R.map (e : V →ₗ[ℂ] V) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T (e.symm x), LinearMap.mem_range_self T _, by simp [LinearEquiv.conj_apply]⟩
  rw [← finTrace_eq_trace _ _ hE, finTrace, ← LinearMap.trace_conj' _ (e.submoduleMap R)]
  congr 1
end GroundTheory.Automorphic.ContragredientTranspose
