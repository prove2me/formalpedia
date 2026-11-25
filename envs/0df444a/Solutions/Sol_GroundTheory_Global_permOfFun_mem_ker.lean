-- Prove2me | solution 1 for GroundTheory.Global.permOfFun_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:51.347797+00:00
-- url     : https://prove2.me/submissions/61dd4158-e02b-46f6-98cb-8625e1acd13e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
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
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.coeff_permOfFun

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
omit [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution {F : X → ℤ} (hF : ∀ (g : G) x, F (g • x) = F x) :
    permOfFun F ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker := by
  rw [AddMonoidHom.mem_ker, cycSub_apply]
  ext x
  simp [Representation.coeff_ofMulAction, hF]
end GroundTheory.Global
