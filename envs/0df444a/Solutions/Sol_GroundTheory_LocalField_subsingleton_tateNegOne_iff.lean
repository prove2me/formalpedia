-- Prove2me | solution 1 for GroundTheory.LocalField.subsingleton_tateNegOne_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:28.355409+00:00
-- url     : https://prove2.me/submissions/058135eb-b7aa-40e1-8feb-a0eda90a5740

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
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}
namespace GroundTheory.LocalField
theorem _root_.solution :
    Subsingleton (TateNegOne G M) ↔ ∀ x : M, tateNorm G M x = 1 → x ∈ augmentation G M := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩
end GroundTheory.LocalField
