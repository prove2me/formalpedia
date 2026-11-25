-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.integral_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:33.357956+00:00
-- url     : https://prove2.me/submissions/2e880ea5-9664-40e8-be4b-22a7a7c3a8d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution (Y : Type) [AddCommGroup Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
    (l : S →ₗ[ℝ] ℝ) (m : ℕ) (x x' : Fin m → Y)
    (h : ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)) (β : S)
    (hβ : ∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) : ∃ z : ℤ, l β = z := by
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  rw [h]; push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _
end GlobalTheory.LatticeBoundTests
