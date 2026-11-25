-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:39.737953+00:00
-- url     : https://prove2.me/submissions/12c570a4-e6a7-46a4-80a5-960361f401da

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_box_antitone
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isClopen_box
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_exists_box_subset
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_exists_mem_box_neg
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ N M : ℤ, M ≤ N ∧ (∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → x ∈ box F M := by
  obtain ⟨hlc, hcs⟩ := hΦ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ (box F (-(m : ℤ)) : Set (Fin 2 → F)) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ (box F (-(m : ℤ)) : Set (Fin 2 → F)))
      (fun m ↦ (isClopen_box _).isOpen) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      exact exists_mem_box_neg x
    · exact Monotone.directed_le fun a b hab ↦ box_antitone (by omega)
  have hloc : ∀ x : Fin 2 → F, ∃ n : ℤ, ∀ h ∈ box F n, Φ (x + h) = Φ x := by
    intro x
    have ho : IsOpen {h : Fin 2 → F | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_box_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh ↦ hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x ↦ {z : Fin 2 → F | z - x ∈ box F (n x)})
    (fun x _ ↦ (((isClopen_box _).isOpen).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨N₀, hN⟩ := (t.image n).exists_le
  set N := max N₀ (-(m : ℤ)) with hNdef
  have hval : ∀ y ∈ tsupport Φ, ∀ h ∈ box F N, Φ (y + h) = Φ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : box F N ≤ box F (n x) :=
      box_antitone ((hN _ (Finset.mem_image_of_mem n hxt)).trans (le_max_left _ _))
    have e1 : Φ y = Φ x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : Φ (y + h) = Φ x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by abel]; exact add_mem hyx (hN' hh))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, -(m : ℤ), le_max_right _ _, fun y h hh ↦ ?_, fun x hx ↦ hm (subset_tsupport Φ hx)⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]
end GroundTheory.Automorphic.GodementSectionLocal
