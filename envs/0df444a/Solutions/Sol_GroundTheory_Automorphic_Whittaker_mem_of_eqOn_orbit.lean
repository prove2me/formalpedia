-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_of_eqOn_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:08.440245+00:00
-- url     : https://prove2.me/submissions/0a661599-424c-4254-b3c8-6adc40054054

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_of_eqOn_orbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [ContinuousSMul H X] [T2Space X] [TopologicalSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hO : U ∩ C = orbit H x₀) {W : Submodule ℂ (X → ℂ)}
    (hWU : W ≤ supportedIn U) {f g : X → ℂ} (hg : g ∈ supportedIn U)
    (hf : f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) (heq : ∀ x ∈ orbit H x₀, g x = f x) :
    g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by
  have hfU : f ∈ supportedIn U := (sup_le hWU inf_le_left) hf
  have := (W ⊔ (supportedIn U ⊓ vanishingOn C)).add_mem hf
    (le_sup_right (a := W) (sub_mem_of_eqOn_orbit hO hg hfU heq))
  simpa using this
end GroundTheory.Automorphic.Whittaker
