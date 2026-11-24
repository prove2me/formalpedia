-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.aesm_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:54:10.378879+00:00
-- url     : https://prove2.me/submissions/980dc8c4-0eac-4520-9f33-5f7ab876667c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_iteratedDeriv_real

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
theorem _root_.solution (hU : IsOpen U)
    (hball : ∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U)
    (G : ℂ → Ω → ℂ) (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U)
    (hm : ∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (G t) μ) {z : ℂ} (hz : z ∈ U) :
    AEStronglyMeasurable (G z) μ := by
  obtain ⟨t, ρ, hρ, hzb, hsub⟩ := hball z hz
  have htU : (t : ℂ) ∈ U := hsub (Metric.mem_ball_self hρ)
  have hterm : ∀ n : ℕ, AEStronglyMeasurable (fun ω => ((n.factorial : ℂ))⁻¹ •
      (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) μ := by
    intro n
    exact ((aesm_iteratedDeriv_real hU n G hd hm t htU).const_smul ((z - t) ^ n)).const_smul
      ((n.factorial : ℂ))⁻¹
  refine aestronglyMeasurable_of_tendsto_ae
    (f := fun N ω => ∑ n ∈ Finset.range N, ((n.factorial : ℂ))⁻¹ •
      (z - t) ^ n • iteratedDeriv n (fun w => G w ω) (t : ℂ)) atTop (fun N => ?_)
    (ae_of_all μ fun ω => ?_)
  · have h := Finset.aestronglyMeasurable_sum (μ := μ) (Finset.range N) (fun n _ => hterm n)
    rw [Finset.sum_fn] at h
    exact h
  · have hs := Complex.hasSum_taylorSeries_on_ball ((hd ω).mono hsub) hzb
    exact hs.tendsto_sum_nat
end GlobalTheory.CompanionTheory.HolMean
