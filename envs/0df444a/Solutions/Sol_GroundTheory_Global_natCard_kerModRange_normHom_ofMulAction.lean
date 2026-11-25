-- Prove2me | solution 1 for GroundTheory.Global.natCard_kerModRange_normHom_ofMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:15.748596+00:00
-- url     : https://prove2.me/submissions/454693bc-6afa-4cda-af9a-1397d9e59a80

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_ker_normHom_le_range_cycSub_ofMulAction
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff


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
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
namespace GroundTheory.Global
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) = 1 := by
  have : Subsingleton (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) := by
    constructor
    intro a b
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    rw [KerModRange.mk_eq_mk_iff]
    exact ker_normHom_le_range_cycSub_ofMulAction hσ (sub_mem a.2 b.2)
  exact Nat.card_of_subsingleton 0
end GroundTheory.Global
