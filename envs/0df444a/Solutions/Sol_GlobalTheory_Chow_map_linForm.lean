-- Prove2me | solution 1 for GlobalTheory.Chow.map_linForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:57.732942+00:00
-- url     : https://prove2.me/submissions/eca124f8-79f6-4008-8f58-5159e3c8d233

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
variable {σ β : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : σ → R) (i : β) :
    map φ (linForm u i) = linForm (fun j => φ (u j)) i := by
  simp [linForm]
end GlobalTheory.Chow
