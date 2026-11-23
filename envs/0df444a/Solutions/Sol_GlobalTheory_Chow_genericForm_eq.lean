-- Prove2me | solution 1 for GlobalTheory.Chow.genericForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.459804+00:00
-- url     : https://prove2.me/submissions/9ba9201d-faf8-4fa7-9ea9-18216d7f3c10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution (i : β) :
    genericForm K σ i = ∑ j, C (X j) * X (i, j) := rfl
end GlobalTheory.Chow
