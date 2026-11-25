-- Prove2me | solution 1 for GroundTheory.Global.coeff_smul_of_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:58.542923+00:00
-- url     : https://prove2.me/submissions/735d715d-d1dc-411e-9934-8701de1509f6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_apply_eq_of_cycSub_eq_zero
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
omit [Fintype G] [Finite X]
namespace GroundTheory.Global
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {f : MonoidAlgebra ℤ X}
    (hf : f ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker) (g : G) (x : X) :
    f.coeff (g • x) = f.coeff x := by
  have h1 := apply_eq_of_cycSub_eq_zero _ hσ (AddMonoidHom.mem_ker.1 hf) g⁻¹
  have h2 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff x) h1
  simpa only [Representation.coeff_ofMulAction, inv_inv] using h2
end GroundTheory.Global
