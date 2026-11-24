-- Prove2me | solution 1 for GlobalTheory.TensHead.MinStab.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.214212+00:00
-- url     : https://prove2.me/submissions/afdef0cb-880d-4fbf-aa04-ab553e10f832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.TensHead
namespace MinStab
theorem _root_.solution {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by
  obtain ⟨hTs, hTmin⟩ := hT
  have hcomm' : ∀ a ∈ A, ∀ x, a (b x) = b (a x) := fun a ha x =>
    LinearMap.congr_fun (hb a ha) x
  refine ⟨?_, ?_⟩
  · intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hcomm' a ha x]
    exact Submodule.mem_map_of_mem (hTs a ha x hx)
  · intro U hU hUle
    have hU' : Stab A (T ⊓ U.comap b) := by
      intro a ha x hx
      refine ⟨hTs a ha x hx.1, ?_⟩
      show b (a x) ∈ U
      rw [← hcomm' a ha x]
      exact hU a ha (b x) hx.2
    rcases hTmin _ hU' inf_le_left with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hUle hu)
      have hx' : x ∈ T ⊓ U.comap b := ⟨hx, hu⟩
      rw [h] at hx'
      rw [(Submodule.mem_bot ℂ).mp hx', map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hUle ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ T ⊓ U.comap b := by rw [h]; exact hx
      exact hx'.2
end MinStab
end GlobalTheory.TensHead
