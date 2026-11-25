-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_isClosed_diff_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:28.859292+00:00
-- url     : https://prove2.me/submissions/1b485736-e8c4-4c7d-9387-f9c9aee4c8e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {H X : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H] [TopologicalSpace X]
  [T2Space X] [LocallyCompactSpace X] [MulAction H X] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty)
    (hZinv : ∀ h : H, ∀ x ∈ Z, h • x ∈ Z) {s : Set X} (hs : s.Countable)
    (hcov : Z ⊆ ⋃ x ∈ s, orbit H x) :
    ∃ x₀ ∈ Z, IsClosed (Z \ orbit H x₀) := by
  have : LocallyCompactSpace Z := hZ.locallyCompactSpace
  have : Nonempty Z := hZne.to_subtype
  have hsc : (s ∩ Z).Countable := hs.mono inter_subset_left
  have : Countable ↥(s ∩ Z) := hsc.to_subtype
  let f : (s ∩ Z : Set X) × ℕ → Set Z := fun i =>
    Subtype.val ⁻¹' ((fun h : H => h • (i.1 : X)) '' compactCovering H i.2)
  have hfc : ∀ i, IsClosed (f i) := fun i =>
    (((isCompact_compactCovering H i.2).image
      (continuous_id.smul continuous_const)).isClosed).preimage continuous_subtype_val
  have hfU : ⋃ i, f i = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨x, hxs, hzx⟩ := mem_iUnion₂.1 (hcov z.2)
    obtain ⟨h, hh⟩ := hzx
    have hxZ : x ∈ Z := by
      have := hZinv h⁻¹ _ z.2
      rwa [← hh, inv_smul_smul] at this
    obtain ⟨k, hk⟩ := mem_iUnion.1 ((iUnion_compactCovering H).symm ▸ mem_univ h :
      h ∈ ⋃ k, compactCovering H k)
    exact mem_iUnion.2 ⟨(⟨x, hxs, hxZ⟩, k), ⟨h, hk, hh⟩⟩
  obtain ⟨⟨⟨x, hxs, hxZ⟩, k⟩, hint⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.1 (isOpen_interior (s := f (⟨x, hxs, hxZ⟩, k)))
  obtain ⟨w, hw⟩ := hint
  have hwW : (w : X) ∈ W := by
    have : w ∈ Subtype.val ⁻¹' W := hW ▸ hw
    exact this
  have hsub : ∀ z : Z, (z : X) ∈ W → (z : X) ∈ orbit H x := by
    intro z hz
    have : z ∈ interior (f (⟨x, hxs, hxZ⟩, k)) := hW ▸ (show z ∈ Subtype.val ⁻¹' W from hz)
    obtain ⟨h, -, hh⟩ := interior_subset this
    exact ⟨h, hh⟩
  refine ⟨x, hxZ, ?_⟩
  have hwO : (w : X) ∈ orbit H x := hsub w hwW
  have key : Z \ orbit H x = Z ∩ ⋂ h : H, (fun z => h • z) ⁻¹' Wᶜ := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_iInter, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hzZ, hzO⟩
      refine ⟨hzZ, fun h hhz => hzO ?_⟩
      have := hsub ⟨h • z, hZinv h z hzZ⟩ hhz
      obtain ⟨k', hk'⟩ := this
      have hk'' : k' • x = h • z := hk'
      refine ⟨h⁻¹ * k', ?_⟩
      show (h⁻¹ * k') • x = z
      rw [mul_smul, hk'', inv_smul_smul]
    · rintro ⟨hzZ, hzW⟩
      refine ⟨hzZ, fun hzO => ?_⟩
      obtain ⟨a, ha⟩ := hzO
      obtain ⟨b, hb⟩ := hwO
      have ha' : a • x = z := ha
      have hb' : b • x = (w : X) := hb
      apply hzW (b * a⁻¹)
      rw [mul_smul, ← ha', inv_smul_smul, hb']
      exact hwW
  rw [key]
  exact hZ.inter (isClosed_iInter fun h =>
    hWo.isClosed_compl.preimage (continuous_const_smul h))
end GroundTheory.Automorphic.ContragredientTranspose
