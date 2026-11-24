-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:54.189154+00:00
-- url     : https://prove2.me/submissions/49ee0a11-8d5d-4895-96f0-6118536992af

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_integral_step

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
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution (hU : IsOpen U) (r : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ z ∈ U, AEStronglyMeasurable (G z) μ) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∫ ω, G w ω ∂μ) z =
      ∫ ω, iteratedDeriv r (fun w => G w ω) z ∂μ := by
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
    intro G _ _ _ z _
    simp only [iteratedDeriv_zero]
  | succ r ih =>
    intro G hd hm hb z hz
    obtain ⟨h1, h2, h3⟩ := integral_step hU G hd hm hb
    have hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U :=
      fun ω => (hd ω).deriv hU
    simp only [iteratedDeriv_succ']
    refine (loc r (deriv (fun w => ∫ ω, G w ω ∂μ)) (fun w => ∫ ω, deriv (fun w' => G w' ω) w ∂μ)
      (fun w hw => (h1 w hw).deriv) hz).trans ?_
    exact ih (fun z ω => deriv (fun w => G w ω) z) hd' h2 h3 z hz
end GlobalTheory.CompanionTheory.HolMean
