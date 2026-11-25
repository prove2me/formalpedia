-- Prove2me | solution 1 for GlobalTheory.T.symbolic_power_in_affine_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:10.833465+00:00
-- url     : https://prove2.me/submissions/beb89106-3843-45c5-aa66-25468fc88fd3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChartStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_relation_homogenises


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s' ∉ SncRes.ideal Q p → s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p → ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises <;> assumption)
end _root_.GlobalTheory.T
