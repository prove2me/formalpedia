-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_kHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:16.904745+00:00
-- url     : https://prove2.me/submissions/e26db165-10a9-4831-8f34-89e3dc5dea3e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*} [Monoid K]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.Automorphic
theorem _root_.solution {τ : Representation ℂ K W} {σ : Representation ℂ K V} {T : W →ₗ[ℂ] V} :
    T ∈ kHom τ σ ↔ ∀ k : K, T ∘ₗ τ k = σ k ∘ₗ T := Iff.rfl
end GroundTheory.Automorphic
