-- Prove2me | solution 1 for GroundTheory.Global.coeff_normHom_ofMulAction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:18.971173+00:00
-- url     : https://prove2.me/submissions/e312dd82-ff53-4a8e-91e9-0b855de6a62a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
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



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]
namespace GroundTheory.Global
theorem _root_.solution (f : MonoidAlgebra ℤ X) (p : X) :
    (normHom (Representation.ofMulAction ℤ G X) f).coeff p = ∑ g : G, f.coeff (g • p) := by
  rw [normHom_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Representation.coeff_ofMulAction]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl
end GroundTheory.Global
