-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_resolvent_laplace_uniqueness_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:50:02.221331+00:00
-- url     : https://prove2.me/submissions/744ad7aa-39d3-473f-bb99-b9cd7f10168b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_resolvent_weighted_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_resolvent_weighted_integral_eq
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * W q x)
        (Set.Ioi (0 : ℝ)) volume ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (W 0 x +
        q * (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume)))
        (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) * W q x ∂volume) =
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-θ * x) *
        (W 0 x + q * (∫ s in Set.Ioc (0 : ℝ) x,
          W 0 s * W q (x - s) ∂volume)) ∂volume) := by
  refine ⟨max 0 (max (Phi ψ 0) (Phi ψ q)) + 1, ?_⟩
  intro θ hθ
  have hz : 0 ≤ θ := by
    linarith [le_max_left (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  have h0 : Phi ψ 0 < θ := by
    linarith [le_max_left (Phi ψ 0) (Phi ψ q),
      le_max_right (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  have hqroot : Phi ψ q < θ := by
    linarith [le_max_right (Phi ψ 0) (Phi ψ q),
      le_max_right (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  exact ⟨((hW q hq).2.2.2.2.2 θ hz hqroot).1,
    source_resolvent_weighted_integrable ψ W hW q θ hq hz h0 hqroot,
    source_resolvent_weighted_integral_eq ψ W hW q θ hq hz h0 hqroot⟩
