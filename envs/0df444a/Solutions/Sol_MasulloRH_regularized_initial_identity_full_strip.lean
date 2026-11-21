-- Prove2me | solution 1 for MasulloRH.regularized_initial_identity_full_strip
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:31:53.877049+00:00
-- url     : https://prove2.me/submissions/df176fb8-4037-4112-be76-52bbcbea3294

/- Endpoint adaptation of the cutoff-limit and limit-assembly proofs by davidloeffler on Prove2Me (13f9ac20-aaae-4457-aa86-128589e4a6ee and 270062f2-0e4a-47b4-a3cc-8e1e5d6ff4f9, Apache-2.0). -/
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_regularized_prime_limit
import Theorems.Thm_MasulloRH_regularized_arch_limit
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open MasulloRH Filter
open scoped Topology

/-- Uniform summable domination allows passage through the full zero sum. -/
private theorem spectralLimit (α : ℝ) (hα : 0 < α)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffSpectral α n s) atTop
      (𝓝 (regularizedSpectral α s)) := by
  obtain ⟨C, hC, hbound⟩ := regularized_spectral_domination_any_window α s hs
  apply tendsto_tsum_of_dominated_convergence
    ((weighted_zero_summability α hα).mul_left C)
  · intro ρ
    have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
    have hwr : ((ρ : ℂ) - 1 / 2).re = (ρ : ℂ).re - 1 / 2 := by simp
    have hm := regularized_mellin_limit s ((ρ : ℂ) - 1 / 2)
      (by rw [hwr]; linarith) (by rw [hwr]; linarith)
    convert hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) using 1 <;>
      simp only [zetaTraceTerm, zeroResolventTerm] <;> congr 3 <;> ring
  · exact .of_forall hbound

set_option autoImplicit false

open MasulloRH Filter
open scoped Topology

/-- Apply the trace formula to each cutoff and pass to the four explicit limits. -/
theorem solution
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    regularizedTraceRHS (1/2) s = zetaLogDeriv s := by
  have hplus := regularized_mellin_limit s (1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hminus := regularized_mellin_limit s (-1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hpolar : Tendsto (fun n : ℕ => cutoffPolar n s) atTop
      (𝓝 (regularizedPolar s)) := by
    convert hplus.add hminus using 1 <;>
      simp only [cutoffPolar, regularizedPolar] <;> congr 2 <;> ring
  have hleft := (regularized_arch_limit s hs).add (regularized_prime_limit s hs)
  have hright := hpolar.sub (spectralLimit (1/2) (by norm_num) s hs)
  have heq : (fun n : ℕ => cutoffArch n s + cutoffPrime n s) =
      (fun n : ℕ => cutoffPolar n s - cutoffSpectral (1/2) n s) := by
    funext n
    exact (trace_formula_rational_full_strip (regularizedTraceTest n s)
      (regularized_test_admissible n s)).2.2.2
  rw [heq] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  unfold regularizedTraceRHS
  linear_combination hlimit