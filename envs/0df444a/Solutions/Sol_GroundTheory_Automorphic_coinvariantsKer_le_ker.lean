-- Prove2me | solution 1 for GroundTheory.Automorphic.coinvariantsKer_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:19.521527+00:00
-- url     : https://prove2.me/submissions/ba008f24-aa59-40c1-a0fb-4f0a410c6d54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet

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
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
omit [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N]
  [TotallyDisconnectedSpace N]
namespace GroundTheory.Automorphic
theorem _root_.solution (K : Subgroup N) :
    coinvariantsKer ρ K ≤ Representation.Coinvariants.ker ρ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨k, v⟩, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker (k : N) v
end GroundTheory.Automorphic
