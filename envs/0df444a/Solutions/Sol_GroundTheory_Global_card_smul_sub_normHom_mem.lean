-- Prove2me | solution 1 for GroundTheory.Global.card_smul_sub_normHom_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:03.87479+00:00
-- url     : https://prove2.me/submissions/f170c595-f653-4dd8-9a55-45916e7e9c99

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_sub_mem_range_cycSub
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.normHom_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : M) :
    (Fintype.card G : ℤ) • x - normHom ρ x ∈ (cycSub ρ σ).range := by
  have : (Fintype.card G : ℤ) • x - normHom ρ x = -∑ g : G, (ρ g x - x) := by
    rw [normHom_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      natCast_zsmul]
    abel
  rw [this]
  exact neg_mem (AddSubgroup.sum_mem _ fun g _ => sub_mem_range_cycSub ρ hσ g x)
end GroundTheory.Global
