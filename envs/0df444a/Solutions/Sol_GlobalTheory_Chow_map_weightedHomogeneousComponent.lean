-- Prove2me | solution 1 for GlobalTheory.Chow.map_weightedHomogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:54.012122+00:00
-- url     : https://prove2.me/submissions/7216cd42-4bda-4122-8b0d-8dac95bf978c

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
theorem _root_.solution {S τ M : Type*} [CommRing S] [AddCommMonoid M]
    (φ : K →+* S) (w : τ → M) (a : M) (f : MvPolynomial τ K) :
    map φ (weightedHomogeneousComponent w a f) = weightedHomogeneousComponent w a (map φ f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp
end GlobalTheory.Chow
