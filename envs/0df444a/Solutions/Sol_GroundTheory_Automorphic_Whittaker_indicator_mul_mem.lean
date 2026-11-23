-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.indicator_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:12.852516+00:00
-- url     : https://prove2.me/submissions/0d440e35-ced0-4f16-8167-f56e8cd339dd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U A : Set X} (hA : IsClopen A) {f : X → ℂ}
    (hf : f ∈ supportedIn U) : (fun x => A.indicator 1 x * f x) ∈ supportedIn U := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : IsLocallyConstant (A.indicator (1 : X → ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const X (1 : ℂ)) hA).isLocallyConstant
    exact h1.comp₂ hf.1.1 (· * ·)
  · refine hf.1.2.mono fun x hx => ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])
  · intro x hx
    refine hf.2 ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])
end GroundTheory.Automorphic.Whittaker
