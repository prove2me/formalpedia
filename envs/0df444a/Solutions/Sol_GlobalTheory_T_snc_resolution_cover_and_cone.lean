-- Prove2me | solution 1 for GlobalTheory.T.snc_resolution_cover_and_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:08.361607+00:00
-- url     : https://prove2.me/submissions/b1111b86-84eb-4506-a7a0-a1878c481e90

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_chart_lifts_package


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package <;> assumption)
end _root_.GlobalTheory.T
