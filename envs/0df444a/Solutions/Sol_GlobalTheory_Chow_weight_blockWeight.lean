-- Prove2me | solution 1 for GlobalTheory.Chow.weight_blockWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:42.164604+00:00
-- url     : https://prove2.me/submissions/18611489-9c2a-4762-822b-318971b72b38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
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
theorem _root_.solution [Fintype σ] (d : β × σ →₀ ℕ) (i : β) :
    Finsupp.weight blockWeight d i = ∑ j, d (i, j) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [hd, he, Finset.sum_add_distrib]
  | single v n =>
    obtain ⟨k, l⟩ := v
    by_cases h : k = i
    · subst h
      simp [Finsupp.weight_single, blockWeight, Finsupp.single_apply]
    · simp [Finsupp.weight_single, blockWeight, Finsupp.single_apply, h, Ne.symm h]
end GlobalTheory.Chow
