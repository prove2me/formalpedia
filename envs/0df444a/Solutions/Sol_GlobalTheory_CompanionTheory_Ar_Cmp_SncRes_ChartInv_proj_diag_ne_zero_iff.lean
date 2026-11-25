-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.proj_diag_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:04.090615+00:00
-- url     : https://prove2.me/submissions/4f8161a9-063d-4c00-88ce-c3d87fcdafd0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
theorem _root_.solution (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by
  simp only [SncRes.proj]
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    have hn : (0 : ℝ) < ‖z ⟨k, i⟩‖ := norm_pos_iff.2 h
    have hpos : (0 : ℝ) < ∑ j, ‖z ⟨k, j⟩‖ ^ 2 := by
      refine lt_of_lt_of_le (pow_pos hn 2) ?_
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hden : ((∑ j, ‖z ⟨k, j⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact div_ne_zero (mul_ne_zero h ((map_ne_zero _).2 h)) hden
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
