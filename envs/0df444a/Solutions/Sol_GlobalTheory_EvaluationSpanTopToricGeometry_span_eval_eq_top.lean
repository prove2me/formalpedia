-- Prove2me | solution 1 for GlobalTheory.EvaluationSpanTopToricGeometry.span_eval_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T14:35:30.208896+00:00
-- url     : https://prove2.me/submissions/0bb36d21-64a4-413f-9bda-495b61ee5a24

import Mathlib

open Submodule

theorem solution {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have hne : (z : X → ℂ) ≠ 0 := by
    intro h
    apply hz
    exact Subtype.ext h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  refine ⟨(LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype, Set.mem_range_self x, ?_⟩
  simpa using hx