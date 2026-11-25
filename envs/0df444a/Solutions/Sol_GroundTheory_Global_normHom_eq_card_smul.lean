-- Prove2me | solution 1 for GroundTheory.Global.normHom_eq_card_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:52.5563+00:00
-- url     : https://prove2.me/submissions/85d029e3-e1dc-4d75-8659-d5f1986c55ba

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_apply_eq_of_cycSub_eq_zero
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
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : M}
    (hx : cycSub ρ σ x = 0) : normHom ρ x = (Fintype.card G : ℤ) • x := by
  rw [normHom_apply, Finset.sum_congr rfl fun g _ => apply_eq_of_cycSub_eq_zero ρ hσ hx g,
    Finset.sum_const, Finset.card_univ, natCast_zsmul]
end GroundTheory.Global
