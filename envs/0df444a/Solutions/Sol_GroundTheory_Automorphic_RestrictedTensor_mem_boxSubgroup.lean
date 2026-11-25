-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_boxSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:26.85575+00:00
-- url     : https://prove2.me/submissions/43c6fd7b-b960-43ef-ad31-10b0b4e848a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct

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
open Filter Function Set Topology
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {K' : ∀ v, Subgroup (G v)} {g : Πʳ v, [G v, K v]} :
    g ∈ boxSubgroup K K' ↔ ∀ v, g v ∈ K' v :=
  Iff.rfl
end GroundTheory.Automorphic.RestrictedTensor
