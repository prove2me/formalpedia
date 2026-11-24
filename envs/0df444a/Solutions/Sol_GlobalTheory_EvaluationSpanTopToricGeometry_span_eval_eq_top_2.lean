-- Prove2me | solution 2 for GlobalTheory.EvaluationSpanTopToricGeometry.span_eval_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:39.932642+00:00
-- url     : https://prove2.me/submissions/9d8826ce-e974-43be-a9ea-2d1900c92786

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EvaluationSpanTopToricGeometry
namespace GlobalTheory.EvaluationSpanTopToricGeometry
theorem _root_.solution {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by

  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set v : V := (Module.evalEquiv ℂ V).symm f with hv
  have hfv : Module.evalEquiv ℂ V v = f := by rw [hv, LinearEquiv.apply_symm_apply]
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    have hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f :=
      hle (Submodule.subset_span ⟨x, rfl⟩)
    rw [LinearMap.mem_ker, ← hfv] at hx
    exact hx
  apply hf0
  rw [← hfv, hv0, map_zero]
end GlobalTheory.EvaluationSpanTopToricGeometry
