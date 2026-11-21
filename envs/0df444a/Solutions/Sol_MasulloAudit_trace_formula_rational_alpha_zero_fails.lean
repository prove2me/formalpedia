-- Prove2me | solution 1 for MasulloAudit.trace_formula_rational_alpha_zero_fails
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:12:03.63818+00:00
-- url     : https://prove2.me/submissions/246db51f-0df6-4088-a1dc-d01bb835cd8d

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_H65K_Platform_Low121_zeros
import Theorems.Thm_RS5_BandZeros_hLine
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

open MeasureTheory Set Filter MasulloRH
open scoped Topology

/-- The regularized cutoff spectral sums converge to the resolvent sum
(dominated convergence; adapted from the accepted proof of
`MasulloRH.omitted_sum_zero_forall_imp_no_omitted_zeros`). -/
private theorem alpha0_spectralLimit (α : ℝ) (hα : 0 < α)
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

/-- The empty window. -/
private instance alpha0_isEmpty : IsEmpty (ZetaZerosInTraceStrip 0) :=
  ⟨fun ρ => (abs_nonneg _).not_gt ρ.property.2.2.2⟩

theorem solution :
    ¬ ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ 0) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip 0, zetaTraceTerm φ 0 ρ := by
  intro H
  -- Step 1: a nontrivial zero on the critical line (platform: 245 zeros with 121 ≤ t ≤ 520).
  obtain ⟨xs, hlen, -, hmem, hzero⟩ := RS5.BandZeros.hLine H65K.Platform.Low121.zeros
  have hne : xs ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  set t := xs.head hne
  have ht : t ∈ xs := List.head_mem hne
  set ρ : ℂ := 1 / 2 + (t : ℂ) * Complex.I with hρ
  have hρre : ρ.re = 1 / 2 := by simp [hρ]
  have hρ0 : ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hρre] at this; norm_num at this
  have hζ : riemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0, hzero t ht, zero_div]
  let z : ZetaZerosInTraceStrip (1 / 2) :=
    ⟨ρ, hζ, by rw [hρre]; norm_num, by rw [hρre]; norm_num, by rw [hρre]; norm_num⟩
  -- Step 2: the α = 0 identity plus the full-strip formula kill the full zero sum.
  have hfull : ∀ φ : ℝ → ℂ, IsRationalTraceTest φ →
      (∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ) = 0 := by
    intro φ hφ
    have h0 := (H φ hφ).2.2.2
    have h1 := (trace_formula_rational_full_strip φ hφ).2.2.2
    have he : (∑' ρ : ZetaZerosInTraceStrip 0, zetaTraceTerm φ 0 ρ) = 0 := tsum_empty
    rw [he, sub_zero] at h0
    have := h1.symm.trans h0
    linear_combination -this
  have hcut : ∀ n : ℕ, cutoffSpectral (1 / 2) n 3 = 0 := fun n =>
    hfull _ (regularized_test_admissible n 3)
  have hspec : regularizedSpectral (1 / 2) 3 = 0 := by
    have hl := alpha0_spectralLimit (1 / 2) (by norm_num) 3 (by norm_num)
    simp only [hcut] at hl
    exact (tendsto_nhds_unique hl tendsto_const_nhds)
  have hspec0 : regularizedSpectral 0 3 = 0 := by
    simp only [regularizedSpectral, tsum_empty]
  have hle : (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS 0 3).re := by
    simp only [regularizedTraceRHS, hspec, hspec0, le_refl]
  -- Step 3: the resolvent test now places every zero in the empty window.
  have hz := (single_resolvent_test 0).1 hle z
  have : (z : ℂ).re = 1 / 2 := hρre
  rw [this, sub_self, abs_zero] at hz
  exact lt_irrefl _ hz
