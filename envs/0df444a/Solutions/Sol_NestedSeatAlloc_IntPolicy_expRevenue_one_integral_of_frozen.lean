-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.expRevenue_one_integral_of_frozen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:36:44.292347+00:00
-- url     : https://prove2.me/submissions/c192ded6-5133-4f95-8426-25d80c0499db

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_frozen_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (s : ℝ) :
    expRevenue P X f p 1 s =
      ∫ ω, condRevenue P X f p 1 (X 1 ω) s ∂P := by
  unfold expRevenue
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  change revenue f p (fun i => X i ω) 1 s =
    condRevenue P X f p 1 (X 1 ω) s
  rw [condRevenue_one_frozen_formula P X f p hM.isProb (X 1 ω) s]
  simp only [revenue]
