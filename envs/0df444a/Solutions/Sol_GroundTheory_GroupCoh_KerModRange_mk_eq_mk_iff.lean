-- Prove2me | solution 1 for GroundTheory.GroupCoh.KerModRange.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:37.947763+00:00
-- url     : https://prove2.me/submissions/1c32cb63-3fe2-478f-a0a7-d36824d28730

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.GroupCoh
namespace KerModRange
theorem _root_.solution {f g : A →+ A} (x y : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = QuotientAddGroup.mk y ↔
      (x : A) - y ∈ g.range := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
end KerModRange
end GroundTheory.GroupCoh
