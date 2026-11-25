-- Prove2me | solution 1 for GroundTheory.LocalField.isElementaryAt_elemSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:07.458864+00:00
-- url     : https://prove2.me/submissions/419404d3-ee10-475f-964e-f66fed3572b8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_right_le_mulSubgroup
import Theorems.Thm_GroundTheory_LocalField_isPGroup_sylowCent

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
theorem _root_.solution (hx : (orderOf x).Coprime p) : IsElementaryAt p (elemSub p x) :=
  ⟨Subgroup.zpowers x, sylowCent p x, left_le_mulSubgroup _, right_le_mulSubgroup _, inferInstance,
    by rwa [Nat.card_zpowers], isPGroup_sylowCent p x, commute_zpowers_sylowCent,
    fun _ hh ↦ hh⟩
end GroundTheory.LocalField
