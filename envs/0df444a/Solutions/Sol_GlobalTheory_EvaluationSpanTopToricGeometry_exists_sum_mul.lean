-- Prove2me | solution 1 for GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:03:55.525837+00:00
-- url     : https://prove2.me/submissions/6132de88-1ce9-4a10-89b5-3f95ae3857e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
import Theorems.Thm_GlobalTheory_EvaluationSpanTopToricGeometry_span_eval_eq_top

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
theorem _root_.solution {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (hV : ∀ y : Y, (fun x : X => F x y) ∈ V)
    (hL : ∀ x : X, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ),
      (∀ i : Fin n, h i ∈ V ∧ k i ∈ L) ∧
        ∀ (x : X) (y : Y), F x y = ∑ i : Fin n, h i x * k i y := by

  let Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ) :=
    { toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  have hΦ : ∀ φ, Φ φ ∈ L := by
    have hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
        ≤ L.comap Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hL x
    intro φ
    exact hle (by rw [span_eval_eq_top V]; trivial)
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩
  intro x y
  have hs := congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl
end GlobalTheory.EvaluationSpanTopToricGeometry
