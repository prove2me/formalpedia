-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.exists_finiteLevel_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:36.69259+00:00
-- url     : https://prove2.me/submissions/9a78f6dc-8802-4911-a351-ad426909f4c6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply_eq
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
import Theorems.Thm_GroundTheory_Global_exists_unitsLevel_subset
import Theorems.Thm_GroundTheory_Global_unitsLevel_antitone
import Theorems.Thm_GroundTheory_Global_unitsLevel_zero
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


attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle

set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz
end GroundTheory.Global.IdeleGroup
