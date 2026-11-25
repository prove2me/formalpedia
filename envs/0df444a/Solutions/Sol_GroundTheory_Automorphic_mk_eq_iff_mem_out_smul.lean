-- Prove2me | solution 1 for GroundTheory.Automorphic.mk_eq_iff_mem_out_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:19.016967+00:00
-- url     : https://prove2.me/submissions/af2c5970-d10a-4e56-b1ca-0e3e214fac02

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
theorem _root_.solution (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]
end GroundTheory.Automorphic
