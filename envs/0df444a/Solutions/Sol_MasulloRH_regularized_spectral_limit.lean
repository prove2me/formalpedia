-- Prove2me | solution 1 for MasulloRH.regularized_spectral_limit
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-20T21:37:09.530594+00:00
-- url     : https://prove2.me/submissions/13f9ac20-aaae-4457-aa86-128589e4a6ee

import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MasulloRH Filter
open scoped Topology

/-- Uniform summable domination allows passage through the full zero sum. -/
theorem solution (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffSpectral α n s) atTop
      (𝓝 (regularizedSpectral α s)) := by
  obtain ⟨C, hC, hbound⟩ := regularized_spectral_domination α hα hαsmall s hs
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
