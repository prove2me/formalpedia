-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.lin_mem_of_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:47.213799+00:00
-- url     : https://prove2.me/submissions/fd80e787-6b81-46d8-a74a-fcb0f53016ff

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SpanEqTopOfForallDotEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_taylor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ J) (h0 : eval t a = 0) :
    ∑ i, C (gradP t a i) * (X i - C (t i)) ∈ J := by
  have h := hJ (ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor t a)
  rw [h0, map_zero, sub_zero] at h
  have h2 := J.sub_mem ha h
  rwa [sub_sub_cancel] at h2
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
