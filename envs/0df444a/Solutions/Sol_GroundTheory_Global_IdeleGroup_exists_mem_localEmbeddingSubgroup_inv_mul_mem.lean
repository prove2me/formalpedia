-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.exists_mem_localEmbeddingSubgroup_inv_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:23.53171+00:00
-- url     : https://prove2.me/submissions/cf30b3aa-9c93-4a8e-9c4a-fa9eaac0586f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteEmbedding_mem_localEmbeddingSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteEmbedding_mem_localEmbeddingSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isTopologicalBasis
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleMap_continuousIdeleMap_apply
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_isTopologicalBasis
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
attribute [local simp] GroundTheory.Global.IdeleMap.continuousIdeleMap_apply
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) *
    ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef
  refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _)
      (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w
          (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _)
          (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv
            (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne
            (by rintro rfl; exact hv hu) _)]
      have hvS := hv
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS
      rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]
      exact hvS.2
end GroundTheory.Global.IdeleGroup
