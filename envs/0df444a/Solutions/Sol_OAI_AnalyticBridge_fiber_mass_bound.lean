-- Prove2me | solution 1 for OAI.AnalyticBridge.fiber_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:53.848396+00:00
-- url     : https://prove2.me/submissions/7b9be301-126d-4d4b-a87a-d176a657d36f

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution {Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (weight : Ω → ℝ) (A : Λ → ℂ) (M : ℝ)
    (hmap : ∀ ω ∈ S, label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, weight ω) ≤ M) :
    (∑ ω ∈ S, weight ω * ‖A (label ω)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    (∑ a ∈ T, ∑ ω ∈ S with label ω = a,
        weight ω * ‖A (label ω)‖ ^ 2) =
      ∑ a ∈ T, (∑ ω ∈ S with label ω = a, weight ω) * ‖A a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        have hl : label ω = a := (Finset.mem_filter.mp hω).2
        rw [hl]
    _ ≤ ∑ a ∈ T, M * ‖A a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hfiber a ha) (sq_nonneg _)
    _ = M * (∑ a ∈ T, ‖A a‖ ^ 2) := by rw [Finset.mul_sum]
end OAI.AnalyticBridge
