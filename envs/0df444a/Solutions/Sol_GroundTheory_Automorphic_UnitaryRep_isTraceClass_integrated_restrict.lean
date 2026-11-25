-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isTraceClass_integrated_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:42:45.362445+00:00
-- url     : https://prove2.me/submissions/7c3612fe-12ae-419b-9403-b5fce70f832b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_isTraceClass_comp_of_isHilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_right
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_right
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_exists_comp
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable {π μ f}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (hT : IsTraceClass (π.integrated μ f)) (j : J) :
    IsTraceClass ((π.restrict (V j) (hinv j)).integrated μ f) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
  set ι : V j →L[ℂ] H := (V j).subtypeL
  have hιι : ∀ x : V j, (ι†) (ι x) = x := fun x =>
    ext_inner_left ℂ fun w => by
      rw [adjoint_inner_right]
      rfl
  have heq : (π.restrict (V j) (hinv j)).integrated μ f = ((ι†).comp A).comp (B.comp ι) := by
    ext1 x
    simp only [comp_apply]
    rw [← hιι ((π.restrict (V j) (hinv j)).integrated μ f x)]
    congr 1
    change (((π.restrict (V j) (hinv j)).integrated μ f x : V j) : H) = _
    rw [integrated_restrict_apply, hAB]
    rfl
  rw [heq]
  exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)
end GroundTheory.Automorphic.UnitaryRep
