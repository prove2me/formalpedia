-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:44.229774+00:00
-- url     : https://prove2.me/submissions/f859db71-6afe-4e42-b66d-08bec2dd5079

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L : Subgroup G} [(L.subgroupOf K).FiniteIndex]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A K) :
    (norm A K L ⟨a, fixedModule_anti hLK ha⟩ : A) = a ^ L.relIndex K := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  rw [coe_norm, finprod_eq_prod_of_fintype]
  have h : ∀ q : K ⧸ L.subgroupOf K, cosetSMul A K L ⟨a, fixedModule_anti hLK ha⟩ q = a := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ => exact ha σ σ.2
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex,
    Subgroup.index_eq_card]
end GroundTheory.LocalField.Abstract
