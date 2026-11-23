-- Prove2me | solution 1 for GlobalTheory.Chow.IsBlockHomogeneous.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:00.955416+00:00
-- url     : https://prove2.me/submissions/9d51961e-3b13-4a52-96a9-7bc8e7cf63ec

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
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
namespace IsBlockHomogeneous
theorem _root_.solution {f : MvPolynomial (β × σ) K} {a b : β → ℕ} (h : f ≠ 0)
    (ha : IsBlockHomogeneous f a) (hb : IsBlockHomogeneous f b) : a = b :=
  IsWeightedHomogeneous.inj_right h ha hb
end IsBlockHomogeneous
end GlobalTheory.Chow
