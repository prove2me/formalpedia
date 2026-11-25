-- Prove2me | solution 1 for GroundTheory.Global.logLatticeProdMap_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:21.602261+00:00
-- url     : https://prove2.me/submissions/8be23eb4-7ab7-4c7b-991b-bcb7a204d992

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Theorems.Thm_GroundTheory_Global_logLatticeProdMap_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coe_logLatticeRep
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField K] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (g : L ≃ₐ[K] L) (x : logLattice L × ℤ) :
    logLatticeProdMap (((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (logLatticeProdMap x) := by
  obtain ⟨m, n⟩ := x
  funext w
  simp [logLatticeProdMap_apply, Representation.prod_apply_apply, coe_logLatticeRep,
    funPermRep_apply]
end GroundTheory.Global
