-- Prove2me | solution 1 for GroundTheory.Global.RestrictedProduct.isOpen_setOf_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:41.671858+00:00
-- url     : https://prove2.me/submissions/968aa016-6be1-4a09-8b18-b8010e29d42b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
open GroundTheory GroundTheory.Global
open GroundTheory.Global.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
namespace GroundTheory.Global.RestrictedProduct
theorem _root_.solution (hAopen : ∀ i, IsOpen (A i)) {V : ∀ i, Set (R i)}
    (hV : ∀ i, IsOpen (V i)) (hVA : ∀ᶠ i in cofinite, V i = A i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} := by
  set S : Set ι := {i | V i = A i}
  have hSf : Sᶜ.Finite := hVA
  have hEq : {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} =
      {x : Πʳ i, [R i, A i] | ∀ i, i ∈ S → x.1 i ∈ A i} ∩
        ⋂ i ∈ Sᶜ, (fun x : Πʳ i, [R i, A i] ↦ x i) ⁻¹' V i := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨fun i hi ↦ (show V i = A i from hi) ▸ h i, fun i _ ↦ h i⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · rw [show V i = A i from hi]
        exact h1 i hi
      · exact h2 i hi
  rw [hEq]
  exact (_root_.RestrictedProduct.isOpen_forall_imp_mem hAopen).inter
    (hSf.isOpen_biInter fun i _ ↦ (hV i).preimage (_root_.RestrictedProduct.continuous_eval i))
end GroundTheory.Global.RestrictedProduct
