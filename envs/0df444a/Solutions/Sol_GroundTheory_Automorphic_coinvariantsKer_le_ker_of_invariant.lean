-- Prove2me | solution 1 for GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:29.767471+00:00
-- url     : https://prove2.me/submissions/b44bfc61-c356-431f-a5bf-f128127e3c3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep

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
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable {ρ}
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup G} {f : V →ₗ[ℂ] W} (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) :
    coinvariantsKer ρ K ≤ LinearMap.ker f := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨k, v⟩, rfl⟩
  simp [hf k k.2 v]
end GroundTheory.Automorphic
