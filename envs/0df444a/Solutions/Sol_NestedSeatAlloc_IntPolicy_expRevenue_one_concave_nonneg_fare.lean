-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.expRevenue_one_concave_nonneg_fare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:42:47.252055+00:00
-- url     : https://prove2.me/submissions/a0c05372-8c7b-49ab-8a5b-d01e05919719

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_integrable_of_seat_model
import Theorems.Thm_concaveOn_of_ae_integral_representation
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_frozen_formula
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_concave_nonneg_fare

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hf1 : 0 ≤ f 1) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1) := by
  let g : Ω → ℝ → ℝ :=
    fun ω s => revenue f p (fun i => X i ω) 1 s
  have hpoint (ω : Ω) :
      g ω = condRevenue P X f p 1 (X 1 ω) := by
    funext s
    rw [condRevenue_one_frozen_formula P X f p hM.isProb (X 1 ω) s]
    rfl
  have hF : ∀ s, 0 ≤ s →
      expRevenue P X f p 1 s = ∫ ω, g ω s ∂P := by
    intro s hs
    rfl
  have hconc : ∀ᵐ ω ∂P,
      ConcaveOn ℝ (Set.Ici 0) (g ω) := by
    apply Filter.Eventually.of_forall
    intro ω
    rw [hpoint ω]
    exact condRevenue_one_concave_nonneg_fare
      P X f p hM hf1 (X 1 ω)
  have hint : ∀ s, 0 ≤ s →
      Integrable (fun ω => g ω s) P := by
    intro s hs
    change Integrable
      (fun ω => revenue f p (fun i => X i ω) 1 s) P
    exact revenue_integrable_of_seat_model P X f p hM hp 0 s hs
  exact concaveOn_of_ae_integral_representation
    P (expRevenue P X f p 1) g hF hconc hint
