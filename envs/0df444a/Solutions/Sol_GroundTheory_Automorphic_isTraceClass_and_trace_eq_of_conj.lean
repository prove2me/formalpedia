-- Prove2me | solution 1 for GroundTheory.Automorphic.isTraceClass_and_trace_eq_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:00.40055+00:00
-- url     : https://prove2.me/submissions/4216062f-f24d-49b1-a53b-1da475ced362

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_isTraceClass_comp_of_isHilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_right
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_left
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_right
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_exists_comp
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution (e : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} {S : K →L[ℂ] K}
    (hT : IsTraceClass T) (hS : ∀ v, S (e v) = e (T v)) : IsTraceClass S ∧ trace S = trace T := by
  have hS' : S = ((e : H →L[ℂ] K).comp T).comp (e.symm : K →L[ℂ] H) := by
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp [hS]
  have hSc : IsTraceClass S := by
    obtain ⟨A, B, hA, hB, hAB⟩ := hT.exists_comp
    rw [hS', hAB, ← comp_assoc, comp_assoc]
    exact isTraceClass_comp_of_isHilbertSchmidt (hA.comp_left _) (hB.comp_right _)
  refine ⟨hSc, ?_⟩
  let b := stdHilbertBasis ℂ H
  let b' : HilbertBasis _ ℂ K := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hb' : ∀ i, b' i = e (b i) := fun i => rfl
  have h1 := hSc.hasSum_trace b'
  have h2 := hT.hasSum_trace b
  refine h1.unique (h2.congr_fun fun i => ?_)
  rw [hb', hS, LinearIsometryEquiv.inner_map_map]
end GroundTheory.Automorphic
