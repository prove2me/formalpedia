-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.proj_eq_of_sameOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:21.276162+00:00
-- url     : https://prove2.me/submissions/f18a15c4-6bcd-4ab1-874f-cdb69b728bd5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : proj z = proj z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext ⟨k, i, j⟩
  simp only [proj]
  have hN : (∑ l, ‖c k * z' ⟨k, l⟩‖ ^ 2 : ℝ) = ‖c k‖ ^ 2 * ∑ l, ‖z' ⟨k, l⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, mul_pow]
  have hcc : c k * starRingEnd ℂ (c k) ≠ 0 :=
    mul_ne_zero (hc k) ((map_ne_zero _).2 (hc k))
  rw [hN, map_mul]
  push_cast
  rw [← Complex.mul_conj', show c k * z' ⟨k, i⟩ * (starRingEnd ℂ (c k) * starRingEnd ℂ (z' ⟨k, j⟩)) =
    (c k * starRingEnd ℂ (c k)) * (z' ⟨k, i⟩ * starRingEnd ℂ (z' ⟨k, j⟩)) by ring]
  exact mul_div_mul_left _ _ hcc
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
