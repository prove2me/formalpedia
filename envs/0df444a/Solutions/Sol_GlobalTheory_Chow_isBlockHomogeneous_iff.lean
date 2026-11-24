-- Prove2me | solution 1 for GlobalTheory.Chow.isBlockHomogeneous_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:29.362847+00:00
-- url     : https://prove2.me/submissions/f472f96f-3a78-412f-8e6a-d794d896a3c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_weight_blockWeight
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
theorem _root_.solution [Fintype σ] {f : MvPolynomial (β × σ) K} {a : β → ℕ} :
    IsBlockHomogeneous f a ↔ ∀ d ∈ f.support, ∀ i, ∑ j, d (i, j) = a i := by
  simp only [IsBlockHomogeneous, IsWeightedHomogeneous, mem_support_iff, funext_iff,
    weight_blockWeight]
end GlobalTheory.Chow
