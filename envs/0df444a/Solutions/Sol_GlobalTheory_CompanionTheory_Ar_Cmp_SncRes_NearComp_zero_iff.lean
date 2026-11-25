-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:04.279885+00:00
-- url     : https://prove2.me/submissions/a7230609-8388-4d39-aa4f-08c056786d78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbedded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularWithBoundaryChoice
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_renPt_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
theorem _root_.solution {P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ f ∈ Q, eval (rep x) f = 0) ↔ ∀ h ∈ ideal Q p, eval (coord P p x) h = 0 := by
  have hiff := mem_conePts_iff_chartIdeal hQ p (rep x) hx
  constructor
  · intro h
    exact renPt_zero _ _ (hiff.1 ⟨(rep_mem x).1, h⟩)
  · intro h
    have h2 : rep x ∈ conePts Q := hiff.2 fun f hf => by
      rw [← eval_renC]
      exact h _ (Ideal.mem_map_of_mem _ hf)
    exact h2.2
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp
