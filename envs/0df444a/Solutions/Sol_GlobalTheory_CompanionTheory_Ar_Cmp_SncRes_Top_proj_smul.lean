-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.proj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:16:05.57178+00:00
-- url     : https://prove2.me/submissions/acb6400b-1f94-4092-b291-a9fd94c2d1c3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
theorem _root_.solution (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    proj (fun q => c q.1 * z q) = proj z := by
  funext q
  obtain ⟨k, i, j⟩ := q
  simp only [proj, norm_mul, mul_pow, ← Finset.mul_sum, map_mul]
  have h1 : ((‖c k‖ ^ 2 : ℝ) : ℂ) = c k * starRingEnd ℂ (c k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : c k * starRingEnd ℂ (c k) ≠ 0 := mul_ne_zero (hc k) (by simpa using hc k)
  rw [Complex.ofReal_mul, h1, ← mul_div_mul_left (z ⟨k, i⟩ * starRingEnd ℂ (z ⟨k, j⟩)) _ h2]
  congr 1
  ring
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
