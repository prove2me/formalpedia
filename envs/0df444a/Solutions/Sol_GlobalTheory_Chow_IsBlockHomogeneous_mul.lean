-- Prove2me | solution 1 for GlobalTheory.Chow.IsBlockHomogeneous.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:26.570804+00:00
-- url     : https://prove2.me/submissions/1fca9184-71a1-4f1e-9334-5ffa04725cad

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
theorem _root_.solution {f g : MvPolynomial (β × σ) K} {a b : β → ℕ}
    (hf : IsBlockHomogeneous f a) (hg : IsBlockHomogeneous g b) :
    IsBlockHomogeneous (f * g) (a + b) := IsWeightedHomogeneous.mul hf hg
end IsBlockHomogeneous
end GlobalTheory.Chow
