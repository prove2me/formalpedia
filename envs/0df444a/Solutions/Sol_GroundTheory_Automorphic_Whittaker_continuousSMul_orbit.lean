-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.continuousSMul_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:41.979113+00:00
-- url     : https://prove2.me/submissions/4e4e388f-0456-47fb-944c-2d965359b3a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit

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
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (x₀ : X) : ContinuousSMul H (orbit H x₀) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  have : ((Subtype.val : orbit H x₀ → X) ∘ fun p : H × orbit H x₀ => p.1 • p.2) =
      fun p : H × orbit H x₀ => p.1 • (p.2 : X) := by
    funext p
    rfl
  rw [this]
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
end GroundTheory.Automorphic.Whittaker
