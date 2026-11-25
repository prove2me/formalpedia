-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.normSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:40.04405+00:00
-- url     : https://prove2.me/submissions/e82d446a-c092-45bb-8f09-91ed0bf9600a

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
theorem _root_.solution {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
