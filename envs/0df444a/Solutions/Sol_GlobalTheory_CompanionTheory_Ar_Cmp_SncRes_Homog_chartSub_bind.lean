-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.chartSub_bind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:36:59.142959+00:00
-- url     : https://prove2.me/submissions/1401e01e-68cd-4b91-9a2f-3bba2e4e0465

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
theorem _root_.solution {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (p : (k : K) → ι k) (h1 : ∀ k, w ⟨k, p k⟩ = 1) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartSub w (bind₁ (lift p) f) = aeval w f := by
  have : (chartSub w).comp (bind₁ (lift p)) = aeval w := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, aeval_X]
    unfold lift
    split_ifs with h
    · obtain ⟨k, i⟩ := q
      simp only at h
      subst h
      rw [h1 k, map_one]
    · simp [chartSub]
  exact DFunLike.congr_fun this f
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
