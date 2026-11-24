-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.support_indicator_mul_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.619069+00:00
-- url     : https://prove2.me/submissions/cf63990f-4768-4445-bf2d-ee47ff896688

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
omit [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {A : Set X} {f : X → ℂ} :
    Function.support (fun x => A.indicator 1 x * f x) ⊆ A ∩ Function.support f := by
  intro x hx
  refine ⟨?_, fun h => hx (by simp [h])⟩
  by_contra h
  exact hx (by simp [Set.indicator_of_notMem h])
end GroundTheory.Automorphic.Whittaker
