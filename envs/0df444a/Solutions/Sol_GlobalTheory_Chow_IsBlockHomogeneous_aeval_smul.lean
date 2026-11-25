-- Prove2me | solution 1 for GlobalTheory.Chow.IsBlockHomogeneous.aeval_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:22.832876+00:00
-- url     : https://prove2.me/submissions/733cd025-4a33-467e-93a6-9693b5035827

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_iff
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
namespace IsBlockHomogeneous
theorem _root_.solution [Fintype σ] [Fintype β] {G : Type*} [CommRing G]
    [Algebra K G] {f : MvPolynomial (β × σ) K} {a : β → ℕ} (h : IsBlockHomogeneous f a)
    (c : β → G) (t : β × σ → G) :
    aeval (fun v => c v.1 * t v) f = (∏ i, c i ^ a i) * aeval t f := by
  rw [isBlockHomogeneous_iff] at h
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [mul_pow, Finset.prod_mul_distrib, Fintype.prod_prod_type,
    Finset.prod_pow_eq_pow_sum, h d hd]
  ring
end IsBlockHomogeneous
end GlobalTheory.Chow
