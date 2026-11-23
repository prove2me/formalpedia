-- Prove2me | solution 1 for GroundTheory.Automorphic.apply_eq_of_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.972982+00:00
-- url     : https://prove2.me/submissions/19cc215e-1016-44dc-87f7-e2ab3a9b9d5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact

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
open scoped Pointwise
variable {G : Type*} [Group G] {E : Type*}
namespace GroundTheory.Automorphic
theorem _root_.solution {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  exact hK g k hk
end GroundTheory.Automorphic
