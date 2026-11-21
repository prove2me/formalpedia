-- Prove2me | solution 1 for MasulloAudit.trace_formula_rational_fixed_window_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:24:32.211916+00:00
-- url     : https://prove2.me/submissions/83606183-50a4-47e0-92bf-b95aa794f108

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

open MeasureTheory Set Filter MasulloRH
open scoped Topology

/-- The regularized cutoff spectral sums converge to the resolvent sum
(dominated convergence, as in `Alpha0_Sol`). -/
private theorem fw_spectralLimit (α : ℝ) (hα : 0 < α)
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

/-- The window identity at `α > 0` places every nontrivial zero in the window. -/
private theorem fw_window_of_identity (α : ℝ) (hα : 0 < α)
    (H : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) :
    ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < α := by
  have hsum : ∀ φ : ℝ → ℂ, IsRationalTraceTest φ →
      (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) =
        ∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ := by
    intro φ hφ
    have h0 := (H φ hφ).2.2.2
    have h1 := (trace_formula_rational_full_strip φ hφ).2.2.2
    have := h1.symm.trans h0
    linear_combination this
  have hcut : ∀ n : ℕ, cutoffSpectral α n 3 = cutoffSpectral (1 / 2) n 3 := fun n =>
    hsum _ (regularized_test_admissible n 3)
  have hlα := fw_spectralLimit α hα 3 (by norm_num)
  have hlh := fw_spectralLimit (1 / 2) (by norm_num) 3 (by norm_num)
  simp only [hcut] at hlα
  have hspec : regularizedSpectral α 3 = regularizedSpectral (1 / 2) 3 :=
    tendsto_nhds_unique hlα hlh
  have hle : (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS α 3).re := by
    simp only [regularizedTraceRHS, hspec, le_refl]
  exact (single_resolvent_test α).1 hle

theorem solution (α : ℝ) (hα : 0 < α)
    (H : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) :
    ∀ s : ℂ, 1 / 2 + α ≤ s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hs1 hs2 hz
  have hw := fw_window_of_identity α hα H
    ⟨s, hz, by linarith, hs2, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  have : |s.re - 1 / 2| = s.re - 1 / 2 := abs_of_nonneg (by linarith)
  simp only [this] at hw
  linarith

#print axioms solution
