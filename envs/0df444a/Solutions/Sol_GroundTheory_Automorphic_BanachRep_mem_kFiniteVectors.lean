-- Prove2me | solution 1 for GroundTheory.Automorphic.BanachRep.mem_kFiniteVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:46.081377+00:00
-- url     : https://prove2.me/submissions/fee78a31-2e82-47c6-9be6-9fb29df02d83

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
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.BanachRep
variable {K' : Type*} [Group K'] [TopologicalSpace K']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (π : BanachRep K' E) (K : Subgroup K')
namespace GroundTheory.Automorphic.BanachRep
theorem _root_.solution {v : E} : v ∈ π.kFiniteVectors K ↔ π.IsKFinite K v := Iff.rfl
end GroundTheory.Automorphic.BanachRep
