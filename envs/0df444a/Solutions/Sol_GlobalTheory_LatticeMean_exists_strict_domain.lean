-- Prove2me | solution 1 for GlobalTheory.LatticeMean.exists_strict_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:59.559659+00:00
-- url     : https://prove2.me/submissions/a4aab4d9-52d7-435d-9f5d-cc86c9b15250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SetAverageProdFundamentalDomainPlaneLatticePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeMean
namespace GlobalTheory.LatticeMean
theorem _root_.solution (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by
  obtain ⟨w₁, w₂, hli, hΛ⟩ := h
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : Set.range b = {w₁, w₂} := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    ext x
    simp [or_comm]
  have hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]
  subst hΛ'
  refine ⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  · exact inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  · exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
end GlobalTheory.LatticeMean
