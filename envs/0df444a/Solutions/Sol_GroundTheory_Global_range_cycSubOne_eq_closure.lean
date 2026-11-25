-- Prove2me | solution 1 for GroundTheory.Global.range_cycSubOne_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:54.1738+00:00
-- url     : https://prove2.me/submissions/9b9d32f9-447f-42a2-8169-3d9e4f62a97b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Theorems.Thm_GroundTheory_Global_apply_sub_self_mem_range_cycSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne ρ σ).range = AddSubgroup.closure {y | ∃ g x, ρ g x - x = y} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact AddSubgroup.subset_closure ⟨σ, x, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    exact apply_sub_self_mem_range_cycSubOne ρ hσ g x
end GroundTheory.Global
