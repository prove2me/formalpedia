-- Prove2me | solution 1 for GroundTheory.LocalField.mk_eq_mk_xIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:25.946241+00:00
-- url     : https://prove2.me/submissions/664adc05-6fea-4614-adfd-32766baed55b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit [Fintype G] hp
namespace GroundTheory.LocalField
theorem _root_.solution (h : elemSub p x) :
    (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) ↔
      x⁻¹ * (h : G) ∈ sylowCent p x := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, ← (sylowCent p x).inv_mem_iff]
  simp [xIn]
end GroundTheory.LocalField
