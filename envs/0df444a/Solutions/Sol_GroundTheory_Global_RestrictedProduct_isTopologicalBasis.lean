-- Prove2me | solution 1 for GroundTheory.Global.RestrictedProduct.isTopologicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:22.62899+00:00
-- url     : https://prove2.me/submissions/702711bc-3ae5-4cce-8c68-495a6be615b1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_isOpen_setOf_forall_mem
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
theorem _root_.solution (hAopen : ∀ i, IsOpen (A i)) :
    IsTopologicalBasis {s : Set (Πʳ i, [R i, A i]) | ∃ V : ∀ i, Set (R i),
      (∀ i, IsOpen (V i)) ∧ (∀ᶠ i in cofinite, V i = A i) ∧ s = {x | ∀ i, x i ∈ V i}} := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨V, hV, hVA, rfl⟩
    exact isOpen_setOf_forall_mem hAopen hV hVA
  · intro x u hxu hu
    set T : Set ι := {i | x i ∈ A i}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr x.2
    obtain ⟨x', hxx'⟩ :=
      _root_.RestrictedProduct.exists_inclusion_eq_of_eventually R A hT (fun i hi ↦ hi)
    have hu' : IsOpen (_root_.RestrictedProduct.inclusion R A hT ⁻¹' u) :=
      hu.preimage (_root_.RestrictedProduct.continuous_inclusion hT)
    rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isOpen_iff] at hu'
    obtain ⟨t, ht, htu⟩ := hu'
    have hx't : (x' : ∀ i, R i) ∈ t := by
      have : x' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [Set.mem_preimage, hxx']
        exact hxu
      rw [← htu] at this
      exact this
    obtain ⟨I, W, hW, hIW⟩ := isOpen_pi_iff.1 ht _ hx't
    let V : ∀ i, Set (R i) := fun i ↦
      (if i ∈ I then W i else Set.univ) ∩ (if i ∈ T then A i else Set.univ)
    refine ⟨{y | ∀ i, y i ∈ V i}, ⟨V, fun i ↦ ?_, ?_, rfl⟩, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · split_ifs with h
        exacts [(hW i h).1, isOpen_univ]
      · split_ifs
        exacts [hAopen i, isOpen_univ]
    · filter_upwards [x.2, I.finite_toSet.compl_mem_cofinite] with i hi hiI
      have hiI' : i ∉ I := hiI
      have hiT : i ∈ T := hi
      simp only [V, if_neg hiI', if_pos hiT, Set.univ_inter]
    · intro i
      rw [← hxx']
      refine ⟨?_, ?_⟩
      · split_ifs with h
        exacts [(hW i h).2, Set.mem_univ _]
      · split_ifs with h
        exacts [eventually_principal.1 x'.2 i h, Set.mem_univ _]
    · intro y hy
      let y' : Πʳ i, [R i, A i]_[𝓟 T] := ⟨y.1, eventually_principal.2 fun i hi ↦ by
        have := (hy i).2
        simp only [if_pos hi] at this
        exact this⟩
      have hy' : y' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [← htu]
        refine hIW fun i hi ↦ ?_
        have := (hy i).1
        simp only [if_pos (Finset.mem_coe.1 hi)] at this
        exact this
      exact hy'
end GroundTheory.Global.RestrictedProduct
