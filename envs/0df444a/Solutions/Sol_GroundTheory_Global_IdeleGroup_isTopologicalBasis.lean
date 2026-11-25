-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isTopologicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:25.718886+00:00
-- url     : https://prove2.me/submissions/5a03bfb4-cd96-4ab7-a039-85344e7abe3b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_isOpen_setOf_forall_mem
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_isTopologicalBasis
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_eq
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_eq
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_units_adicCompletionIntegers
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
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution :
    IsTopologicalBasis {s : Set (IdeleGroup K) |
      ∃ (U : ∀ w : InfinitePlace K, Set (w.Completion)ˣ)
        (V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ),
        (∀ w, IsOpen (U w)) ∧ (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in cofinite, V v =
          ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) ∧
        s = {x | (∀ w, infiniteProj w x ∈ U w) ∧ ∀ v, finiteProj v x ∈ V v}} := by
  set e := prodRestrictedEquiv K
  set p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hVO, rfl⟩
    have h1 : IsOpen {x : IdeleGroup K | ∀ w, infiniteProj w x ∈ U w} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w ↦ (hU w).preimage (continuous_infiniteProj w)
    have h2 : IsOpen {x : IdeleGroup K | ∀ v, finiteProj v x ∈ V v} := by
      simp only [finiteProj_eq]
      exact (RestrictedProduct.isOpen_setOf_forall_mem
        (fun v ↦ isOpen_units_adicCompletionIntegers K v) hV hVO).preimage
          (continuous_snd.comp e.continuous)
    exact h1.inter h2
  · intro x u hxu hu
    have hu' : IsOpen (e.symm ⁻¹' u) := hu.preimage e.symm.continuous
    have hxu' : e x ∈ e.symm ⁻¹' u := by simpa using hxu
    obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := isOpen_prod_iff.1 hu' (e x).1 (e x).2 hxu'
    obtain ⟨_, ⟨V, hV, hVO, rfl⟩, hxV, hVb⟩ :=
      (RestrictedProduct.isTopologicalBasis
        (fun v ↦ isOpen_units_adicCompletionIntegers K v)).exists_subset_of_mem_open hxb hb
    have ha' : IsOpen (p.symm ⁻¹' a) := ha.preimage p.symm.continuous
    have hxa' : p (e x).1 ∈ p.symm ⁻¹' a := by
      change p.symm (p (e x).1) ∈ a
      exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
        (p.symm_apply_apply (e x).1)).mpr hxa
    obtain ⟨U, hU, hUa⟩ := isOpen_pi_iff'.1 ha' _ hxa'
    refine ⟨{y | (∀ w, infiniteProj w y ∈ U w) ∧ ∀ v, finiteProj v y ∈ V v},
      ⟨U, V, fun w ↦ (hU w).1, hV, hVO, rfl⟩, ⟨fun w ↦ ?_, fun v ↦ ?_⟩, ?_⟩
    · rw [infiniteProj_eq]
      exact (hU w).2
    · rw [finiteProj_eq]
      exact hxV v
    · rintro y ⟨hyU, hyV⟩
      have hya : (e y).1 ∈ a := by
        have : p (e y).1 ∈ p.symm ⁻¹' a := hUa fun w _ ↦ by
          rw [← infiniteProj_eq]
          exact hyU w
        change p.symm (p (e y).1) ∈ a at this
        exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
          (p.symm_apply_apply (e y).1)).mp this
      have hyb : (e y).2 ∈ b := hVb fun v ↦ by
        rw [← finiteProj_eq]
        exact hyV v
      have := hab (Set.mk_mem_prod hya hyb)
      simpa using this
end GroundTheory.Global.IdeleGroup
