-- Prove2me | solution 1 for GlobalTheory.EvaluationSpanTop.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:45.910558+00:00
-- url     : https://prove2.me/submissions/f0fbd7f2-ae95-4546-9411-6830d01079e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanEvalEqTop
import Theorems.Thm_GlobalTheory_EvaluationSpanTop_span_eval_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvaluationSpanTop
open Module
namespace GlobalTheory.EvaluationSpanTop
theorem _root_.solution : ∀ {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ ↥W], ∃ (m : ℕ) (b : Fin m → κ → ℂ) (c : Fin m → κ →₀ ℂ), (∀ (i : Fin m), b i ∈ W) ∧ ∀ v ∈ W, ∀ (k' : κ), v k' = ∑ i : Fin m, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) * b i k' := by
  intro κ W _
  let B := Module.finBasis ℂ W
  have hspan := span_eval_eq_top W
  have hc : ∀ i, ∃ c : κ →₀ ℂ, Finsupp.linearCombination ℂ
      (fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) c = B.coord i := by
    intro i
    have : B.coord i ∈ Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) := by
      rw [hspan]; trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp.mp this).imp fun c hc => by
      rw [Finsupp.linearCombination_apply]; exact hc
  choose c hc using hc
  refine ⟨Module.finrank ℂ W, fun i => (B i : κ → ℂ), c, fun i => (B i).2, ?_⟩
  intro v hv k'
  have hsum := B.sum_repr ⟨v, hv⟩
  have key : ∀ i, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) = B.repr ⟨v, hv⟩ i := by
    intro i
    rw [← Basis.coord_apply, ← hc i, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    simp [LinearMap.sum_apply]
  simp_rw [key]
  have h2 := congrArg (fun w : W => (w : κ → ℂ) k') hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm
end GlobalTheory.EvaluationSpanTop
