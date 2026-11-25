-- Prove2me | solution 1 for GroundTheory.GroupCoh.sum_eq_sum_quotient_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:31.838139+00:00
-- url     : https://prove2.me/submissions/976ee8fd-db32-4504-bff7-0847c4fbf78b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Fintype G] (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    {β : Type*} [AddCommMonoid β] (f : G → β) :
    ∑ g : G, f g = ∑ c : G ⧸ S, ∑ s : S, f (c.out * s) := by
  let e : (G ⧸ S) × S ≃ G :=
    { toFun := fun x => x.1.out * x.2
      invFun := fun g => ((g : G ⧸ S), cosetPart S g)
      left_inv := fun x => by
        obtain ⟨c, s⟩ := x
        ext
        · exact mk_out_mul S c s
        · simp only [cosetPart_out_mul]
      right_inv := fun g => out_mul_cosetPart S g }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
end GroundTheory.GroupCoh
