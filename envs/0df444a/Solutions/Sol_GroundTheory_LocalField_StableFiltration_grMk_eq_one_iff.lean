-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.grMk_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:44.477033+00:00
-- url     : https://prove2.me/submissions/7c79d850-62ba-40b2-b8fe-f933c2a25a1a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (x : S.F n) : S.grMk n x = 1 ↔ (x : V) ∈ S.F (n + 1) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
end GroundTheory.LocalField.StableFiltration
