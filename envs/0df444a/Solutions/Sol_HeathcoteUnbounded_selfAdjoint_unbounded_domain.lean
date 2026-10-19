-- Prove2me | solution 1 for HeathcoteUnbounded.selfAdjoint_unbounded_domain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:23:48.277683+00:00
-- url     : https://prove2.me/submissions/9d684af4-ddbf-467e-9abc-e4124e49380e

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi
open MeasureTheory HeathcoteUnbounded Set

theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hunb : ¬ ∃ k : ℝ, ∀ ψ : A.domain, ‖A ψ‖ ≤ k * ‖(ψ : H)‖) :
    Dense (A.domain : Set H) ∧ A.domain ≠ ⊤ := by
  refine ⟨hA.dense_domain, fun htop => hunb ?_⟩
  set e := LinearEquiv.ofTop A.domain htop
  set f : H →ₗ[ℂ] H := A.toFun.comp e.symm.toLinearMap
  have hgraph : (f.graph : Set (H × H)) = (A.graph : Set (H × H)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · intro h
      refine ⟨e.symm x, ?_, ?_⟩
      · simp [e]
      · rw [h]; rfl
    · rintro ⟨z, hz, hzy⟩
      have : e.symm x = z := by
        apply Subtype.ext; simp [e, ← hz]
      rw [← hzy, ← this]; rfl
  have hcl : IsClosed (f.graph : Set (H × H)) := by
    rw [hgraph]; exact hA.isClosed
  have hcont : Continuous f := LinearMap.continuous_of_isClosed_graph f hcl
  let F : H →L[ℂ] H := ⟨f, hcont⟩
  refine ⟨‖F‖, fun ψ => ?_⟩
  have h1 : F ψ = A ψ := by
    show A.toFun (e.symm (ψ : H)) = A ψ
    congr 1
  rw [← h1]
  exact F.le_opNorm _
