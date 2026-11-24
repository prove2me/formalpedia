-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:17.374731+00:00
-- url     : https://prove2.me/submissions/798a1d02-f98f-4dbb-b058-74ad86726163

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_series_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
variable {κ : Type} {U : Set ℂ}
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution (hU : IsOpen U) (r : ℕ) : ∀ (F : κ → ℂ → ℂ),
    (∀ k, DifferentiableOn ℂ (F k) U) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∑' k, F k w) z = ∑' k, iteratedDeriv r (F k) z := by
  have loc : ∀ (n : ℕ) (f g : ℂ → ℂ), Set.EqOn f g U →
      Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) U := by
    intro n
    induction n with
    | zero =>
      intro f g h z hz
      simp only [iteratedDeriv_zero]
      exact h hz
    | succ n ih =>
      intro f g h z hz
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hz) (ih f g h))
  induction r with
  | zero =>
    intro F _ _ z _
    simp only [iteratedDeriv_zero]
  | succ r ih =>
    intro F hF hb z hz
    obtain ⟨_, hder, hb'⟩ := series_step hU F hF hb
    have hF' : ∀ k, DifferentiableOn ℂ (deriv (F k)) U := fun k => (hF k).deriv hU
    simp only [iteratedDeriv_succ']
    rw [loc r (deriv (fun w => ∑' k, F k w)) (fun w => ∑' k, deriv (F k) w)
      (fun w hw => hder w hw) hz]
    exact ih (fun k => deriv (F k)) hF' hb' z hz
end GlobalTheory.CompanionTheory.HolMean
