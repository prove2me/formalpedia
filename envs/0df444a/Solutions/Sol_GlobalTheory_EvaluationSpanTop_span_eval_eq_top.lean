-- Prove2me | solution 1 for GlobalTheory.EvaluationSpanTop.span_eval_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:08.566816+00:00
-- url     : https://prove2.me/submissions/7f5c9a38-747f-4f70-a046-8355b99a3ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanEvalEqTop

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
theorem _root_.solution {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) = ⊤ := by
  set S := Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  have hco : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    have : ∀ k, (x : κ → ℂ) k = 0 := fun k =>
      hx _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [Submodule.mem_bot]
    ext k
    simpa using this k
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
  rw [← this, hco, Submodule.dualAnnihilator_bot]
end GlobalTheory.EvaluationSpanTop
