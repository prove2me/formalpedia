-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.comap_parabolicMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:31.326739+00:00
-- url     : https://prove2.me/submissions/f931d15b-d1a8-4734-a779-56fe22f77188

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_coe_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
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
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun =
      map (parabolicMkHomeomorph β) ((μ𝔪.comap (leviChart β).toFun).prod μ𝔫) := by
  ext S hS
  have hSP := (parabolicChart F n β).measurableEmbedding.measurableSet_image.2 hS
  have hΘ : Measurable (parabolicMkHomeomorph (F := F) β) :=
    (parabolicMkHomeomorph β).continuous.measurable
  have hE : Measurable (coordEquiv (F := F) β) := (coordEquiv β).continuous.measurable
  rw [(parabolicChart F n β).measurableEmbedding.comap_apply, parabolicMeasure,
    map_apply hE hSP, map_apply hΘ hS, Measure.prod_apply (hE hSP), Measure.prod_apply (hΘ hS)]
  set G : (LeviIndex n β → F) → ℝ≥0∞ := fun a =>
    μ𝔫 (Prod.mk a ⁻¹' (coordEquiv β ⁻¹' ((parabolicChart F n β).toFun '' S))) with hG
  have hslice : ∀ m : levi F n β,
      μ𝔫 (Prod.mk m ⁻¹' (parabolicMkHomeomorph β ⁻¹' S)) = G ((leviChart β).toFun m) := by
    intro m
    rw [hG]
    congr 1
    ext u
    simp only [Set.mem_preimage]
    show parabolicMk β m u ∈ S ↔ coordEquiv β ((leviChart β).toFun m, u) ∈ _
    rw [coe_coordEquiv, ← parabolicChart_parabolicMk,
      (parabolicChart F n β).isOpenEmbedding.injective.mem_set_image]
  have hsupp : Function.support G ⊆ Set.range (leviChart β).toFun := by
    intro a ha
    obtain ⟨u, p, -, hp⟩ : ∃ u, coordEquiv β (a, u) ∈ (parabolicChart F n β).toFun '' S := by
      by_contra h
      push Not at h
      apply ha
      rw [hG]
      convert measure_empty (μ := μ𝔫)
      ext u
      simpa using h u
    refine ⟨leviProj F n β p, ?_⟩
    have e := congrArg (fun y => ((coordAddEquiv β).symm y).1) hp
    simp only [coe_coordEquiv, AddEquiv.symm_apply_apply] at e
    rw [← e]
    funext s
    rw [leviChart_apply, leviProj_apply, if_pos s.2]
    rfl
  rw [show (fun x : levi F n β => μ𝔫 (Prod.mk x ⁻¹' (parabolicMkHomeomorph β ⁻¹' S))) =
      fun m => G ((leviChart β).toFun m) from funext hslice,
    ← (leviChart β).measurableEmbedding.lintegral_map, (leviChart β).measurableEmbedding.map_comap,
    setLIntegral_eq_of_support_subset hsupp]
end GroundTheory.Automorphic.GodementJacquet
