-- Prove2me | solution 1 for GroundTheory.GroupCoh.natCard_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:24.405553+00:00
-- url     : https://prove2.me/submissions/5e6e5937-7039-4309-a9d7-404466cf0bbc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_range_le_ker

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
theorem _root_.solution {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) :
    Nat.card f.ker = Nat.card (KerModRange f g) * Nat.card g.range := by
  have h1 := AddSubgroup.card_mul_index (g.range.addSubgroupOf f.ker)
  have h2 : Nat.card (g.range.addSubgroupOf f.ker) = Nat.card g.range :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (range_le_ker hfg)).toEquiv
  rw [← h1, h2, mul_comm]
  rfl
end GroundTheory.GroupCoh
