-- Prove2me | solution 1 for OAI.AnalyticBridge.weighted_cauchy_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:53.1532+00:00
-- url     : https://prove2.me/submissions/9150b691-2d16-48c7-8204-63aac6a568b2

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
theorem _root_.solution
    (S : Finset Ω) (w U V : Ω → ℂ) :
    ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
  have htri : ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
      ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
    calc
      ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
          ∑ ω ∈ S, ‖w ω * U ω * star (V ω)‖ := norm_sum_le _ _
      _ = ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
        apply Finset.sum_congr rfl
        intro ω hω
        simp [ ]
  have hnonneg : 0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ :=
    Finset.sum_nonneg (by intro ω hω; positivity)
  have hsq :
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2 ≤
        (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
          (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun ω hω => by positivity) (fun ω hω => by positivity)
    intro ω hω
    (convert le_refl ((‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2) using 1 ; ring)
  exact (sq_le_sq₀ (norm_nonneg _) hnonneg).2 htri |>.trans hsq
end OAI.AnalyticBridge
