-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_of_isZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:47.448446+00:00
-- url     : https://prove2.me/submissions/2f106c04-a6a1-46e3-aaa6-a1a2c5781ed7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
import Theorems.Thm_GroundTheory_GroupCoh_hom_nsmul_apply
import Theorems.Thm_GroundTheory_GroupCoh_hom_zero_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_free
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_free
import Theorems.Thm_P2M_GroundTheory_GroupCoh_CohTrivial_of_shortExact_X__518f55910066
import Theorems.Thm_P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
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
variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let π : Rep.free ℤ G A.V ⟶ A := Rep.freeLift ℤ G A fun a => a
  have hπ : Function.Surjective π.hom := fun a =>
    ⟨Finsupp.single a (MonoidAlgebra.single 1 1), by
      have hmod : A.hV2 = AddCommGroup.toIntModule A.V := Subsingleton.elim _ _
      simp only [π]
      simp
      rw [hmod]
      exact one_zsmul a⟩
  have : Epi π := (Rep.epi_iff_surjective π).2 hπ
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
      mono_f := equalizer.ι_mono
      epi_g := inferInstanceAs (Epi π) }
  have hfree : ∀ x : Rep.free ℤ G A.V, p • x = 0 → x = 0 := fun x hx =>
    (smul_eq_zero.mp hx).resolve_left (Fact.out : p.Prime).ne_zero
  have hK : ∀ x : S.X₁, p • x = 0 → x = 0 := by
    have hinj : Function.Injective (kernel.ι π).hom :=
      (Rep.mono_iff_injective _).1 equalizer.ι_mono
    intro x hx
    apply hinj
    rw [hom_zero_apply]
    apply hfree
    rw [← hom_nsmul_apply, hx, hom_zero_apply]
  have h2 : TateAcyclic S.X₂ := tateAcyclic_free A.V
  have k₁ : IsZero (tateCohomology S.X₁ (q + 1)) :=
    h₁.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS q) (isIso_δ_of_tateAcyclic hS h2 q)).symm
  have k₂ : IsZero (tateCohomology S.X₁ (q + 1 + 1)) :=
    h₂.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS (q + 1))
      (isIso_δ_of_tateAcyclic hS h2 (q + 1))).symm
  obtain ⟨tK, cK⟩ :=
    tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion hG S.X₁ hK (q + 1) k₁ k₂
  have t3 := TateAcyclic.of_shortExact_X₁ hS h2 tK
  have c2 : CohTrivial S.X₂ := cohTrivial_free A.V
  have c3 := CohTrivial.of_shortExact_X₁ hS c2 cK
  exact ⟨t3, c3⟩
end GroundTheory.GroupCoh
