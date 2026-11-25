-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.eq_sum_shells
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:18.240379+00:00
-- url     : https://prove2.me/submissions/f0918e41-9a30-4b07-bee8-346ecda38bf0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_box_antitone
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
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ} {N M : ℤ} (hMN : M ≤ N)
    (hinv : ∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) (hsupp : ∀ x, Φ x ≠ 0 → x ∈ box F M) :
    Φ = (∑ m ∈ Finset.Ico M N, (shellAt F m).indicator Φ) + Φ 0 • boxInd F N := by
  have hcount : ∀ x ∈ box F M, ∀ n, M ≤ n →
      (∑ m ∈ Finset.Ico M n, (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x) +
        boxInd F n x = 1 := by
    intro x hx n hn
    induction n, hn using Int.leInduction with
    | base => simp [boxInd, Set.indicator_of_mem hx]
    | succ n hn ih =>
      have hI : Finset.Ico M (n + 1) = insert n (Finset.Ico M n) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp), add_comm (Set.indicator _ _ x), add_assoc, ← ih]
      congr 1
      by_cases h1 : x ∈ box F (n + 1)
      · have h0 : x ∈ box F n := box_antitone (by omega) h1
        have hs : x ∉ shellAt F n := fun h ↦ h.2 h1
        simp [boxInd, Set.indicator_of_mem h1, Set.indicator_of_mem h0,
          Set.indicator_of_notMem hs]
      · by_cases h0 : x ∈ box F n
        · have hs : x ∈ shellAt F n := ⟨h0, h1⟩
          simp [boxInd, Set.indicator_of_notMem h1, Set.indicator_of_mem h0,
            Set.indicator_of_mem hs]
        · have hs : x ∉ shellAt F n := fun h ↦ h0 h.1
          simp [boxInd, Set.indicator_of_notMem h1, Set.indicator_of_notMem h0,
            Set.indicator_of_notMem hs]
  funext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ box F M
  · have hind : ∀ m, (shellAt F m).indicator Φ x =
        (shellAt F m).indicator (1 : (Fin 2 → F) → ℂ) x * Φ x := by
      intro m
      by_cases h : x ∈ shellAt F m
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    have hbox : Φ 0 * boxInd F N x = boxInd F N x * Φ x := by
      by_cases h : x ∈ box F N
      · have := hinv 0 x h
        rw [zero_add] at this
        simp [boxInd, Set.indicator_of_mem h, this]
      · simp [boxInd, Set.indicator_of_notMem h]
    simp only [hind, hbox, ← Finset.sum_mul, ← add_mul, hcount x hx N hMN, one_mul]
  · have h0 : Φ x = 0 := by
      by_contra h
      exact hx (hsupp x h)
    have hN : x ∉ box F N := fun h ↦ hx (box_antitone hMN h)
    simp only [h0, boxInd, Set.indicator_of_notMem hN, mul_zero, add_zero]
    refine (Finset.sum_eq_zero fun c _ ↦ ?_).symm
    by_cases h : x ∈ shellAt F c
    · rw [Set.indicator_of_mem h, h0]
    · rw [Set.indicator_of_notMem h]
end GroundTheory.Automorphic.GodementSectionLocal
