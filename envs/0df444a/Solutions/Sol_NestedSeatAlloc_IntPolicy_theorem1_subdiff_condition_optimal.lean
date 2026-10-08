-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_subdiff_condition_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T06:20:45.774388+00:00
-- url     : https://prove2.me/submissions/1fc4f436-6f8f-4341-b5d7-e998225a6998
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by
  have hconc := theorem1_conditional_concavity P X f p hM hp h20
  have hopt := theorem1_global_optimality P X f p hM hp h20
  exact ⟨hconc, hopt⟩
