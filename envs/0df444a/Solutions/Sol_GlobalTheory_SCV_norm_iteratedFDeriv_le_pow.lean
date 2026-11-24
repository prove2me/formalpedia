-- Prove2me | solution 1 for GlobalTheory.SCV.norm_iteratedFDeriv_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:44.065145+00:00
-- url     : https://prove2.me/submissions/dc6c7678-e1df-43b7-80e9-52d655c36e59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_fderiv_le_of_ball
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_iteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {δ M : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∀ x : E, closedBall x (n * δ) ⊆ U → (∀ z ∈ closedBall x (n * δ), ‖f z‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f x‖ ≤ M * (2 / δ) ^ n := by
  induction n with
  | zero =>
    intro x _ hM
    simpa using hM x (by simp)
  | succ n ih =>
    intro x hx hM
    have hsub : ∀ y ∈ ball x δ, closedBall y (n * δ) ⊆ closedBall x ((n + 1 : ℕ) * δ) :=
      fun y hy => closedBall_subset_closedBall' (by
        push_cast
        linarith [mem_ball.mp hy])
    have hball : ball x δ ⊆ U := fun y hy =>
      hx (hsub y hy (mem_closedBall_self (by positivity)))
    rw [← norm_fderiv_iteratedFDeriv]
    refine (norm_fderiv_le_of_ball (M := M * (2 / δ) ^ n) hδ
      ((differentiableOn_iteratedFDeriv hU hf n).mono hball)
      fun y hy => ih y ((hsub y hy).trans hx) fun z hz => hM z (hsub y hy hz)).trans_eq ?_
    ring
end GlobalTheory.SCV
