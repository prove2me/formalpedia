-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_winOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:46.283666+00:00
-- url     : https://prove2.me/submissions/4af154cc-af4d-46dd-8f83-ac7e77cfd95b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_mOrbit
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsWinProj_apply_of_mem

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable {ρ} {e : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) : IsSimpleUnder (winOps ρ e) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hx0' : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [eq_top_iff]
  intro y _
  have hle : Submodule.span ℂ (range fun m => ρ m (x : V)) ≤
      (p.map (LinearMap.range e).subtype).comap e := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨winOp ρ e m x, hp _ ⟨m, rfl⟩ x hx, rfl⟩
  have := hle (mem_span_mOrbit (ρ := ρ) hx0' (y : V))
  obtain ⟨z, hz, hzy⟩ := this
  have : z = y := Subtype.ext (hzy.trans (he.apply_of_mem y.2))
  rwa [← this]
end GroundTheory.Automorphic.RestrictedTensor
