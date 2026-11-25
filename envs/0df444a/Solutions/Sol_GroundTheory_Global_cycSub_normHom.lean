-- Prove2me | solution 1 for GroundTheory.Global.cycSub_normHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:47.064813+00:00
-- url     : https://prove2.me/submissions/8ee20b59-de38-487c-ad94-0b5714fc1446

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
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


attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [AddCommGroup M]
namespace GroundTheory.Global
theorem _root_.solution [Fintype G] (ρ : Representation ℤ G M) (σ : G) (x : M) :
    cycSub ρ σ (normHom ρ x) = 0 := by
  simp only [normHom, cycSub, LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply,
    LinearMap.id_apply, Representation.self_norm_apply, sub_self]
end GroundTheory.Global
