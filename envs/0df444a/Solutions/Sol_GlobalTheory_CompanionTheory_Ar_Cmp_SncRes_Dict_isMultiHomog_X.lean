-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict.isMultiHomog_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:29:34.768621+00:00
-- url     : https://prove2.me/submissions/e2f31bfd-c23e-4ca7-b9ee-07ce5c33fc61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturated
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
theorem _root_.solution [DecidableEq K] (s : Σ k, ι k) :
    IsMultiHomog (X s : MvPolynomial (Σ k, ι k) ℂ) (Pi.single s.1 1 : K → ℕ) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := s
  by_cases h : k = k₀
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ i, (Finsupp.single (⟨k₀, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0 := fun i => by
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact h (congrArg Sigma.fst e).symm
    simp [this, Pi.single_apply, h]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
