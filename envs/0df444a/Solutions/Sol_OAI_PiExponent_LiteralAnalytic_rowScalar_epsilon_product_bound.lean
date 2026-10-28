-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_epsilon_product_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:21:51.68999+00:00
-- url     : https://prove2.me/submissions/0992140e-a3c1-40ba-bb15-29c46dfbb945

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution : ¬ (∀ {σ : Type} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (a β : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν : ℝ) (hC : 0 ≤ C)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)),
    ‖∏ i, ε i ^ (a i - β i - (e i : ℕ))‖ ≤
      Real.exp (C * (∑ i, (a i : ℝ)) - ν *
        (MatrixTranslationBounds.weight w (fun i => a i) -
          MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)))) := by
  intro H
  have h := H (σ := PUnit) (fun _ => 0) 0 (Finsupp.single PUnit.unit 1) (fun _ => 0) (fun _ => -1) 0 1
    le_rfl (fun _ => by simp [Real.exp_nonneg])
  simp [MatrixTranslationBounds.weight] at h
  have : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  linarith
