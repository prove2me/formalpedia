-- Prove2me | solution 1 for GlobalTheory.T.snc_resolution_local_chart_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:31.328433+00:00
-- url     : https://prove2.me/submissions/504a18ee-9d6e-4195-b0d3-92a1cf800a18

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomial
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_ChartInv_chart_coord_ratio


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
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio <;> assumption)
end _root_.GlobalTheory.T
