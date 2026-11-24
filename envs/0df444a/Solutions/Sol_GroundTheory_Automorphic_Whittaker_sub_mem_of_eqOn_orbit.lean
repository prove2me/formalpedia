-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sub_mem_of_eqOn_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:50.438296+00:00
-- url     : https://prove2.me/submissions/8b2875a8-0ce8-4dd8-8fb2-ee26c815c5ea

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
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
theorem _root_.solution (hO : U ∩ C = orbit H x₀) {f g : X → ℂ} (hf : f ∈ supportedIn U)
    (hg : g ∈ supportedIn U) (heq : ∀ x ∈ orbit H x₀, f x = g x) :
    f - g ∈ supportedIn U ⊓ vanishingOn C := by
  refine ⟨(supportedIn U).sub_mem hf hg, fun x hxC => ?_⟩
  by_cases hxU : x ∈ U
  · have hx : x ∈ orbit H x₀ := hO ▸ ⟨hxU, hxC⟩
    simp [heq x hx]
  · have h1 : f x = 0 := Function.notMem_support.1 fun h => hxU (hf.2 h)
    have h2 : g x = 0 := Function.notMem_support.1 fun h => hxU (hg.2 h)
    simp [h1, h2]
end GroundTheory.Automorphic.Whittaker
