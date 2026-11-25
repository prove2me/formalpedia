-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.lift_mem_conePts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:45:54.284187+00:00
-- url     : https://prove2.me/submissions/89f14722-c4b2-467e-bbb6-cace7499c7c7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_lift_vec
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_rep_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal


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
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) ∈ conePts P := by
  rw [lift_vec p x hx]
  exact (conePts_of_chartIdeal hP p _
    ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))).1
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
