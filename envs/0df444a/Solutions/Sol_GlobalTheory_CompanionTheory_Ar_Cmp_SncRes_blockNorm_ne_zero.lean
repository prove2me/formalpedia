-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.blockNorm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:57.953281+00:00
-- url     : https://prove2.me/submissions/7f910b05-f6bc-4331-a398-2cc680a6b2de

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
theorem _root_.solution {z : (Σ k, ι k) → ℂ} {k : K} {j : ι k} (hj : z ⟨k, j⟩ ≠ 0) :
    ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have h1 : 0 < ‖z ⟨k, j⟩‖ ^ 2 := by positivity
  have h2 : ‖z ⟨k, j⟩‖ ^ 2 ≤ ∑ l, ‖z ⟨k, l⟩‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖z ⟨k, l⟩‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ j)
  exact Complex.ofReal_ne_zero.2 (lt_of_lt_of_le h1 h2).ne'
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
