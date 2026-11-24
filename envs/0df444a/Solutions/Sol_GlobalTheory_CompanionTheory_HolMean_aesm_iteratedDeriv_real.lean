-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.aesm_iteratedDeriv_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:15.978167+00:00
-- url     : https://prove2.me/submissions/7c58f4a3-da95-409f-821b-c6d5b89ffe1b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_deriv

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
theorem _root_.solution (hU : IsOpen U) (n : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (G t) μ) →
    ∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => iteratedDeriv n (fun w => G w ω) t) μ := by
  induction n with
  | zero =>
    intro G _ hm t ht
    simp only [iteratedDeriv_zero]
    exact hm t ht
  | succ n ih =>
    intro G hd hm t ht
    simp only [iteratedDeriv_succ']
    have hd' : ∀ ω, DifferentiableOn ℂ (fun z => deriv (fun w => G w ω) z) U :=
      fun ω => (hd ω).deriv hU
    have hm' : ∀ s : ℝ, (s : ℂ) ∈ U →
        AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) (s : ℂ)) μ := by
      intro s hs
      refine aesm_deriv hU G hd hs (fun x hx => ?_)
      have h := hm (s + x) (by rw [Complex.ofReal_add]; exact hx)
      rw [Complex.ofReal_add] at h
      exact h
    exact ih (fun z ω => deriv (fun w => G w ω) z) hd' hm' t ht
end GlobalTheory.CompanionTheory.HolMean
