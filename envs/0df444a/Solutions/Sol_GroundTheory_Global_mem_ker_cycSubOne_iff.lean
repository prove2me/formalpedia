-- Prove2me | solution 1 for GroundTheory.Global.mem_ker_cycSubOne_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:04.318988+00:00
-- url     : https://prove2.me/submissions/dd282220-290b-4546-82fd-82fbbc401844

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Theorems.Thm_GroundTheory_Global_apply_eq_self_of_generator

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
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : V) :
    x ∈ (cycSubOne ρ σ).ker ↔ ∀ g, ρ g x = x := by
  rw [AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero]
  exact ⟨fun h => apply_eq_self_of_generator ρ hσ h, fun h => h σ⟩
end GroundTheory.Global
